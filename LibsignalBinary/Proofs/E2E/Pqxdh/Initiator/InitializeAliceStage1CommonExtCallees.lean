/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.Leaves
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCallees
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtA
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1CommonExtB
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesDecode
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract

/-!
# Contract-Backed Initiator Callee Proofs (`tripleRatchetProgAtExt`)

Proves contract-backed `subroutine_ok` specifications on `tripleRatchetProgAtExt` for
`spqr_chain_params`, `<SessionState>::set_unacknowledged_kyber_pre_key_id`,
`<SessionState>::set_kyber_ciphertext`, `<kem::Ciphertext>::serialize`,
`<PrivateKey>::derive_public_key_bytes`, `<StaticSecret as Drop>::drop`, and
`<RootKey>::create_chain`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.E2E.Pqxdh

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.HMAC CryptoGames.HKDF
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore (rodata_0x7ff6a)

section StackSplits

private theorem stackAt_extract_split_calcExt (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 752 ∗ stackAt sp initAliceCalcStackExt :=
  initAlice_stackAt_split sp 752 initAliceCalcStackExt (by decide)

private theorem stackAt_extract_split_expandExt (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 336 ∗ stackAt sp expandMultiInfoStackExt :=
  initAlice_stackAt_split sp 336 expandMultiInfoStackExt (by decide)

private theorem stackAt_extract_split_allocExt (sp : BitVec 64) :
    stackAt sp extractStackExt =
      memRegion (sp - 17360#64) 13264 ∗ stackAt sp allocHookStack :=
  initAlice_stackAt_split sp 13264 allocHookStack (by decide)

private theorem stackAt_kemSerialize48_ext (sp : BitVec 64) :
    stackAt sp tryCloneFromRefStack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 :=
  LibsignalTripleRatchet.stackAt_split_cells sp 4096 6 (by decide)

private theorem memRegion_1569_split_ext (a : BitVec 64) :
    memRegion a 1569 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ memRegion (a + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
    memRegion_split a 1 1568 (by decide), memRegion_one]

end StackSplits

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- `spqr_chain_params` (`5` insns, pure) on `tripleRatchetProgAtExt b ext`. -/
theorem spqrChainParams_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrChainParamsName)
      spqrChainParamsSpec := by
  unfold spqrChainParamsSpec
  have hfn : libsignalSessionCode.fnOff spqrChainParamsName =
      num% (ls_off% "libsignal_protocol::ratchet::spqr_chain_params") :=
    spqrChainParams_fnOff
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.spqrChainParams b
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_protocol::ratchet::spqr_chain_params")) 20
  dsimp only [tripleRatchetProgAtExt]
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    spqrChainParamsName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init v s0
  subst h
  wp_steps
  wp_done

/-- `<SessionState>::set_unacknowledged_kyber_pre_key_id` (`13` insns, pure) on
`tripleRatchetProgAtExt b ext`. -/
theorem setUnackKyberPreKeyId_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setUnackKyberPreKeyIdName)
      setUnackKyberPreKeyIdSpec := by
  unfold setUnackKyberPreKeyIdSpec
  have hfn : libsignalSessionCode.fnOff setUnackKyberPreKeyIdName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id")
  code_fetches CryptoVerification.libsignalSessionCode setUnackKyberPreKeyId b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id")) 52
  dsimp only [tripleRatchetProgAtExt]
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    setUnackKyberPreKeyIdName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨statePtr, cap, kyberPreKeyId⟩
  dsimp only at *
  subst h_1 h_2
  wp_pull_exists
  have hcond : ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
    rw [ProofLib.conditionHolds_eq_addsPState64]
    exact beq_eq_false_iff_ne.mpr ‹_›
  wp_steps
  wp_done

/-- `<SessionState>::set_kyber_ciphertext` (`None` prior ciphertext, `22` insns, pure) on
`tripleRatchetProgAtExt b ext`. -/
theorem setKyberCiphertext_none_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setKyberCiphertextName)
      setKyberCiphertextNoneSpec := by
  unfold setKyberCiphertextNoneSpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff setKyberCiphertextName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext")
  code_fetches CryptoVerification.libsignalSessionCode setKyberCiphertext b
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext")) 88
  dsimp only [tripleRatchetProgAtExt]
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    setKyberCiphertextName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨statePtr, ctPtr, ctLen⟩
  dsimp only at *
  subst h h_1 h_2
  wp_pull_exists
  wp_steps
  wp_done

private theorem sepWPp_pure_mid_extCallees {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post postP : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) post postP) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post postP := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

/-- `<kem::Ciphertext>::serialize` on `tripleRatchetProgAtExt b ext` under contract-backed
`AllocHooks`, `shim`, and `memcpy`. -/
theorem kemCiphertextSerialize_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext)
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2"
      SignalSession.CliExt.shimSpec)
    (hMemcpy : HookSat ext "memcpy" SignalSession.CliExt.memcpySpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr kemCiphertextSerializeName)
      (kemCiphertextSerializeSpec A) := by
  unfold kemCiphertextSerializeSpec
  simp only [stackAt_kemSerialize48_ext]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff kemCiphertextSerializeName =
      num% (ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize") :=
    kemCiphertextSerialize_fnOff
  have hshim := initAlice_shim_ok_at_ext (b := b) hShim
    (name := kemCiphertextSerializeName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := initAlice_alloc_ok_at_ext (b := b) hA
    (name := kemCiphertextSerializeName)
    (k := num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hmemcpy := initAlice_memcpy_region_ok_at_ext (b := b) hMemcpy
    (name := kemCiphertextSerializeName)
    (k := num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    (by rw [hfn, (ls_stub% "memcpy")])
  have hpanic := initAlice_panic_at_raw_vec_handle_error_ext (b := b) (ext := ext)
    (name := kemCiphertextSerializeName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  dsimp only [pqxdhShimSpec] at hshim
  dsimp only [initAliceMemcpyRegionExtSpec] at hmemcpy
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.kemCiphertextSerialize b
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize")) 144
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmemcpy hpanic ⊢
  clear hfn hA hShim hMemcpy
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr kemCiphertextSerializeName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init g s0
  obtain ⟨hdrPtr, boxPtr, ctBytes⟩ := g
  dsimp only at *
  subst h_1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  have hct_lt : ctBytes.length < 2 ^ 64 := by rw [h]; decide
  apply SepWPp.of_sepWP (mid := entry + 72#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_extCallees fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (LibsignalTripleRatchet.allocFailedIn_of_eq
          (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_1569_split_ext, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid_extCallees fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← h]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, ctBytes)
    wp_steps
    simp only [pointsToBytes_cons]
    wp_done

/-- `<PrivateKey>::derive_public_key_bytes` on `tripleRatchetProgAtExt b ext` at
`pqxdhHookStackExt` (`16384` B) under `HookSat ext pubFromSecretName (CliExt.pubFromSecretSpec C)`. -/
theorem derive_public_key_bytes_ok_pqxdh_ext {b : BitVec 64} {C : Crypto}
    {ext : String → Option (State → State)}
    (hPub : HookSat ext pubFromSecretName (SignalSession.CliExt.pubFromSecretSpec C)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr derivePublicKeyBytesName)
      (derivePublicKeyBytesStackSpec C.pubKey pqxdhHookStackExt) := by
  have hsat : HookSat ext pubFromSecretName
      (derivePublicKeyBytesStackSpec C.pubKey pqxdhHookStackExt) := by
    rcases hPub with ⟨fn, hfn, hok⟩
    refine ⟨fn, hfn, initAlice_hookOk_map
      (fun (x : DerivePublicKeyBytesCall) => (x.secret, x.sec, x.out)) hok ?_ ?_⟩
    · intro x R s0 hpre
      dsimp only [derivePublicKeyBytesStackSpec, pqxdhHookStackExt,
        SignalSession.CliExt.pubFromSecretSpec, SignalSession.CliExt.withStack, extHookStack]
        at hpre ⊢
      simpa only [Nat.reducePow, sepConj_assoc] using hpre
    · intro x R s0 sf _ hpost
      dsimp only [derivePublicKeyBytesStackSpec, pqxdhHookStackExt,
        SignalSession.CliExt.pubFromSecretSpec, SignalSession.CliExt.withStack, extHookStack]
        at hpost ⊢
      simpa only [Nat.reducePow, sepConj_assoc] using hpost
  have hpub0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr pubFromSecretName + BitVec.ofNat 64 0)
      (derivePublicKeyBytesStackSpec C.pubKey pqxdhHookStackExt) :=
    hook_ok_at (hname := pubFromSecretName) (name := pubFromSecretName) (k := 0) rfl
      (Nat.add_zero _)
      (by rw [(ls_stub% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from")]; decide)
      (fun H => by
        rw [(ls_stub% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from")]
        exact (ls_hook% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from") H)
      (by decide +kernel)
      (by rcases hsat with ⟨fn, hfn, hok⟩; exact ⟨fn, by rw [← hfn], hok⟩)
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr pubFromSecretName + 0#64) _ at hpub0
  rw [BitVec.add_zero] at hpub0
  exact derive_public_key_bytes_ok_of_contract_stack pqxdhHookStackExt hpub0

/-- `<StaticSecret as Drop>::drop` stub spec at `pqxdhHookStackExt` (`16384` B). -/
def initAliceStaticDropExtSpec : Spec (BitVec 64) :=
  SignalSession.CliExt.zeroizeSpec

theorem initAlice_staticDrop_ok_at_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hSt : HookSat ext staticDropName SignalSession.CliExt.zeroizeSpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff staticDropName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      SignalSession.CliExt.zeroizeSpec :=
  hook_ok_at (hname := staticDropName) rfl hk
    (by rw [(ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")]; decide)
    (fun H => by
      rw [(ls_stub% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")]
      exact (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop") H)
    (by decide +kernel)
    (by rcases hSt with ⟨fn, hfn, hok⟩; exact ⟨fn, by rw [← hfn], hok⟩)

/-- Stack budget of `<RootKey>::create_chain` on `tripleRatchetProgAtExt`:
`576 + extractStackExt = 576 + 17360 = 17936` B. -/
@[simp, arm64_norm]
abbrev pqxdhCreateChainStackExt : Nat := 576 + extractStackExt

/-- Contract-backed `<RootKey>::create_chain` on `tripleRatchetProgAtExt img.base ext`
at `pqxdhCreateChainStackExt` (`17936` B). -/
theorem pqxdh_createChain_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : InitAliceAgreeHooks C A ext)
    (hHkdf : HkdfContractsExt img C.F ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName)
      ((Keys.createChainSpecAt C A extractStackExt).inImage img) := by
  have hfn : libsignalSessionCode.fnOff createChainName =
      num% (ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain") :=
    (ls_lemma% fnOff "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")
  have hct : ConsumeMessageKeyTransfer.CtEqROOkExt32 img.base ext :=
    ConsumeMessageKeyTransfer.ctEqRO_ok_ext32 img.base hH.blackBox
  have hag0 := ResponderCore.calculateAgreement_rodata_ok_ext himg hct
    hH.alloc hH.dh hH.sharedDrop hH.shim hH.staticDrop
  have hag_rel := Keys.subroutine_ok_rel_rebase hag0
    (ls_lemma% fnOff "<libsignal_core::curve::PrivateKey>::calculate_agreement") hfn
    (k := num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")) (by decide)
  have hag : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName +
        BitVec.ofNat 64 (num% (ls_off% "<libsignal_core::curve::PrivateKey>::calculate_agreement" -
          ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")))
      ((Keys.calculateAgreementCallSpecAt C.X A extractStackExt).inImage img) := by
    refine subroutine_ok_outcome_intro fun ⟨ourA, our, theirA, their, ret, sp⟩ R s0 hpc hrun hpre hsp => ?_
    dsimp only [Spec.inImage, Keys.calculateAgreementCallSpecAt] at hpre
    rw [stackAt_extract_split_calcExt sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨hF, ⟨hx0, hx1, hx8, hsp_eq⟩, hpre⟩
    subst hsp_eq
    have hro := rodata_0x7ff6a himg hF.1.roData hpre
    have hpre' : s0.mem ⊨
        (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
          (Keys.calculateAgreementSpecAt C.X A initAliceCalcSubStackExt).pre
            ⟨ourA, our, theirA, their, ret⟩ s0) ∗
          (memRegion (s0.sp - 17360#64) 752 ∗ R) := by
      dsimp only [Keys.calculateAgreementSpecAt, initAliceCalcStackExt] at hro ⊢
      have hcomm :
          (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            (⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
              (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
              memRegion ret 24 ∗ A.pool ∗ stackAt s0.sp (160 + initAliceCalcSubStackExt))) ∗
            (memRegion (s0.sp - 17360#64) 752 ∗ R) =
          ⌜s0.readReg64 .x0 = ourA ∧ s0.readReg64 .x1 = theirA ∧ s0.readReg64 .x8 = ret⌝ ∗
            (((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
              ((ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
                memRegion ret 24 ∗ memRegion (s0.sp - 17360#64) 752 ∗ A.pool ∗
                stackAt s0.sp (160 + initAliceCalcSubStackExt) ∗ R)) := by
        ac_rfl
      rw [hcomm, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx8⟩, by ac_nf at hro ⊢⟩
    refine hag_rel.mono_outcome ⟨ourA, our, theirA, their, ret⟩
      (memRegion (s0.sp - 17360#64) 752 ∗ R) s0 hpc hrun hpre' hsp fun sf hout => ?_
    rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨c, hex, hq⟩ | ⟨hoom, hq⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [Keys.calculateAgreementSpecAt, Spec.inImage,
        Keys.calculateAgreementCallSpecAt, initAliceCalcStackExt] at hq ⊢
      rw [stackAt_extract_split_calcExt s0.sp]
      have hq' : sf.mem ⊨
          ((img.base + bv% (ls_xref% 0x3e748 0x3e74c)) ↦ᵣ List.replicate 32 0#8) ∗
            ((⌜sf.trace = s0.trace⌝ ∗
              (ourA ↦ₛ our.bytes.toList) ∗ (theirA ↦ₛ their.bytes.toList) ∗
              calculateAgreementResultAt A ret (calculateAgreement C.X their our) ∗
              A.pool ∗ (memRegion (s0.sp - 17360#64) 752 ∗
                stackAt s0.sp (160 + initAliceCalcSubStackExt))) ∗ R) := by
        ac_nf at hq ⊢
      exact Satisfies.of_sep_right hq'
    · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
      dsimp only [Keys.calculateAgreementSpecAt, Spec.inImage,
        Keys.calculateAgreementCallSpecAt] at hq ⊢
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      rcases hq with ⟨hpan_prop, hmem⟩
      refine ⟨hpan_prop, ?_⟩
      have hmem' : sf.mem ⊨ (anyHeap ∗ memRegion (s0.sp - 17360#64) 752) ∗ R := by
        simpa only [sepConj_assoc] using hmem
      exact Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem'
    · exact (not_satisfies_false_sepConj hq).elim
    · exact (not_satisfies_false_sepConj hq).elim
  have hext0 := Keys.subroutine_ok_rel_rebase (extract_ok_ext' img C ext himg hHkdf)
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract") hfn
    (k := num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")) (by decide)
  have hext_c : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName +
        BitVec.ofNat 64 (num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" -
          ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")))
      (Keys.extractKey32StackSpecAt C.F img extractStackExt) := by
    refine subroutine_ok_map hext0 ?_
    rintro ⟨ret, saltA, rk, ikmA, ikm, sp⟩ R s0 hpre
    dsimp only [Keys.extractKey32StackSpecAt] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hx4, hsp, hsalt_ne, hikm⟩, hpre⟩
    refine ⟨⟨ret, saltA, some (Ratchet.keyToBytesVec32 rk), ikmA, ikm⟩, R, ?_, ?_⟩
    · dsimp only [Spec.inImage, extractSpecExt, optSaltAt]
      subst hsp
      rw [eq_true hsalt_ne, pure_true, emp_sepConj, Keys.pointsTo_keyVec_toList]
      simp only [Option.isSome_some, reduceCtorEq, IsEmpty.forall_iff, forall_const, true_and,
        sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx2, hx3, hx4, hikm⟩, by arm64_sep_close⟩
    · intro sf hpost
      dsimp only [Spec.inImage, extractSpecExt, ExtractGhost.prk, optSaltAt,
        Keys.extractKey32StackSpecAt] at hpost ⊢
      subst hsp
      rw [eq_true hsalt_ne, pure_true, emp_sepConj, Keys.pointsTo_keyVec_toList] at hpost
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, by arm64_sep_close⟩
  have hexp0 := Keys.subroutine_ok_rel_rebase (expand_multi_info_ok_ext' img C ext hHkdf)
    (ls_lemma% fnOff "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info") hfn
    (k := num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")) (by decide)
  have hexp_c : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName +
        BitVec.ofNat 64 (num% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::expand_multi_info" -
          ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")))
      (Keys.expandCellsStackSpecAt C.F img 8 extractStackExt) := by
    refine subroutine_ok_map hexp0 ?_
    rintro ⟨hkdfA, prk, infoHdrA, infoA, info, okmA, sp⟩ R s0 hpre
    dsimp only [Keys.expandCellsStackSpecAt] at hpre
    rw [stackAt_extract_split_expandExt sp, ← ProofLib.memRegion_cells okmA 8 (by decide)] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨hF, hx0, hx1, hx2, hx3, hsp, hprk, hinfo, hlen⟩, hpre⟩
    refine ⟨⟨hkdfA, prk, infoHdrA, infoA, info, okmA, 8 * 8⟩,
      memRegion (sp - 17360#64) 336 ∗ R, ?_, ?_⟩
    · dsimp only [Spec.inImage, expandMultiInfoSpecExt]
      subst hsp
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hF.1, hF.2⟩, ⟨hx0, hx1, hx2, hx3, hprk, hinfo, hlen⟩, by arm64_sep_close⟩
    · intro sf hpost
      dsimp only [Spec.inImage, expandMultiInfoSpecExt, Keys.expandCellsStackSpecAt] at hpost ⊢
      rw [stackAt_extract_split_expandExt sp]
      subst hsp
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      have hE := sepConj_mono_left
        (Q := ((infoHdrA ↦₆₄ infoA) ∗ ((infoHdrA + 8#64) ↦₆₄ BitVec.ofNat 64 info.length) ∗
          (infoA ↦ᵣ info) ∗ (okmA ↦ₛ hkdfExpand C.F prk info (8 * 8)) ∗
          stackAt s0.sp expandMultiInfoStackExt ∗ memRegion (s0.sp - 17360#64) 336) ∗ R)
        (Keys.hmacCore_entails_cells C.F hkdfA prk)
      replace hpost := Satisfies.mono hE (by simpa only [sepConj_assoc] using hpost)
      exact ⟨htr, by arm64_sep_close⟩
  have hdealloc_raw := initAlice_dealloc_ok_at_ext (b := img.base) hH.alloc
    (name := createChainName)
    (k := num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_dealloc")])
  have hdealloc0 := Keys.deallocAllocStack_of_rustDealloc_rebase hdealloc_raw
  have hdealloc_c : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "<libsignal_protocol::ratchet::keys::RootKey>::create_chain")))
      (Keys.deallocStackSpecAt A img extractStackExt) := by
    refine subroutine_ok_map hdealloc0 ?_
    rintro ⟨p, size, align, sp⟩ R s0 hpre
    dsimp only [Keys.deallocStackSpecAt] at hpre
    rw [stackAt_extract_split_allocExt sp] at hpre
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rcases hpre with ⟨⟨_, hx0, hx1, hx2, _, _, _, hsp⟩, hpre⟩
    refine ⟨⟨p, size, align, sp⟩, memRegion (sp - 17360#64) 13264 ∗ R, ?_, ?_⟩
    · dsimp only [Keys.deallocAllocStackSpec]
      simp only [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hsp⟩, by arm64_sep_close⟩
    · intro sf hpost
      dsimp only [Keys.deallocAllocStackSpec, Keys.deallocStackSpecAt] at hpost ⊢
      rw [stackAt_extract_split_allocExt sp]
      simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      rcases hpost with ⟨htr, hpost⟩
      exact ⟨htr, by arm64_sep_close⟩
  exact Keys.createChain_ok_of_hooks_gen (callStack := extractStackExt) (by decide)
    himg hag hext_c hexp_c hdealloc_c

theorem pqxdh_createChain_ok_of_externsOk_raw {img : Obj.Image}
    {P0 : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr createChainName)
      ((Keys.createChainSpecAt P0.C A extractStackExt).inImage img) :=
  pqxdh_createChain_ok_ext himg (InitAliceAgreeHooks.of_externsOk hOk)
    (HkdfContractsExt.of_externsOk_raw img hOk)

theorem pqxdh_createChain_ok_of_externsOk {img : Obj.Image}
    {P0 : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hOk : SignalSession.CliExternsOk P0 A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (SignalSession.cliExternsWith ext)).fnAddr createChainName)
      ((Keys.createChainSpecAt P0.C A extractStackExt).inImage img) :=
  pqxdh_createChain_ok_ext himg (InitAliceAgreeHooks.of_cliExternsOk hOk)
    (HkdfContractsExt.of_externsOk img hOk)

namespace Initiator

abbrev spqrChainParams_ok_ext := @Pqxdh.spqrChainParams_ok_ext
abbrev setUnackKyberPreKeyId_ok_ext := @Pqxdh.setUnackKyberPreKeyId_ok_ext
abbrev setKyberCiphertext_none_ok_ext := @Pqxdh.setKyberCiphertext_none_ok_ext
abbrev kemCiphertextSerialize_ok_ext := @Pqxdh.kemCiphertextSerialize_ok_ext
abbrev derive_public_key_bytes_ok_pqxdh_ext := @Pqxdh.derive_public_key_bytes_ok_pqxdh_ext
abbrev initAlice_staticDrop_ok_at_ext := @Pqxdh.initAlice_staticDrop_ok_at_ext
abbrev pqxdhCreateChainStackExt := Pqxdh.pqxdhCreateChainStackExt
abbrev pqxdh_createChain_ok_ext := @Pqxdh.pqxdh_createChain_ok_ext
abbrev pqxdh_createChain_ok_of_externsOk_raw := @Pqxdh.pqxdh_createChain_ok_of_externsOk_raw
abbrev pqxdh_createChain_ok_of_externsOk := @Pqxdh.pqxdh_createChain_ok_of_externsOk

end Initiator

end CryptoVerification.E2E.Pqxdh
