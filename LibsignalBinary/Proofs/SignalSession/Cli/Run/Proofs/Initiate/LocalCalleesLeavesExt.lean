/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.Leaves
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.SessionRecordCallees
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.LeavesDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SmallCalleesDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Extern-Parameterized Leaf Callee Contracts for `initiate`

Proves `CliExternsOk P A ext`-parameterized `subroutine_ok` theorems on
`tripleRatchetProgAtExt img.base (cliExternsWith ext)` for the leaf callees of `initiate`:
`spqr_chain_params`, `<SessionState>::set_unacknowledged_kyber_pre_key_id`,
`<SessionState>::set_kyber_ciphertext`, `<curve25519::PrivateKey>::derive_public_key_bytes`,
`<SessionState>::{new, with_receiver_chain, with_sender_chain}`, `<kem::Ciphertext>::serialize`,
and `<SessionRecord>::promote_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli

/-! ## Shared specification definitions -/

/-- Image call invariant `img.FrozenLoaded s ∧ s.symtab = img.symtab`. -/
abbrev LeafImgCallInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

/-- `CliExternsOk`-compatible `<kem::Ciphertext>::serialize` contract. -/
def kemCiphertextSerializeExtSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (hdrPtr, boxPtr, ctBytes) s =>
    ⌜s.readReg64 .x0 = hdrPtr ∧ ctBytes.length = 1568⌝ ∗
    (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗
    (boxPtr ↦ₛ ctBytes) ∗ A.pool ∗ stackAt s.sp tryCloneFromRefStackX
  post := fun (hdrPtr, boxPtr, ctBytes) s0 sf =>
    ∃∗ tempPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = tempPtr ∧
        sf.readReg64 .x1 = 1569#64 ∧ tempPtr ≠ 0#64⌝ ∗
      (hdrPtr ↦₆₄ boxPtr) ∗ ((hdrPtr + 8#64) ↦₆₄ 1568#64) ∗ (boxPtr ↦ₛ ctBytes) ∗
      (tempPtr ↦ₛ (8#8 :: ctBytes)) ∗ A.live tempPtr 1569 1 ∗
      A.pool ∗ stackAt s0.sp tryCloneFromRefStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Stack-parameterized empty-record `SessionRecord::promote_state` contract. -/
def promoteStateEmptyExtSpec (img : Obj.Image) (stk : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (recPtr, srcPtr, bs) s =>
    ⌜LeafImgCallInv img s⌝ ∗
    ⌜s.readReg64 .x0 = recPtr ∧ s.readReg64 .x1 = srcPtr ∧ bs.length = 344⌝ ∗
    ((recPtr + 0x18#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (recPtr + 0x20#64) 336 ∗
    (srcPtr ↦ₛ bs) ∗
    stackAt s.sp stk
  post := fun (recPtr, srcPtr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    ((recPtr + 0x18#64) ↦ₛ bs) ∗
    (srcPtr ↦ₛ bs) ∗
    stackAt s0.sp stk

/-! ## Pure code-only leaf callees -/

theorem spqrChainParams_ext_ok {b : BitVec 64} {extP : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b extP)
      ((tripleRatchetProgAtExt b extP).fnAddr Pqxdh.spqrChainParamsName)
      Pqxdh.spqrChainParamsSpec := by
  unfold Pqxdh.spqrChainParamsSpec
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.spqrChainParams b
    (Rust.withPanics extP)
    (ls_lemma% fnOff "libsignal_protocol::ratchet::spqr_chain_params")
    (num% (ls_off% "libsignal_protocol::ratchet::spqr_chain_params")) 0 20
  wp_init v s0
  examples_generalize_entry
  examples_hide_fetches
  subst h
  wp_steps
  wp_done

private theorem cond_eq_adds_1_false_ext {cap : BitVec 64} (hne : cap + 1#64 ≠ 0#64) :
    ConditionHolds .EQ (addsPState64 cap 1#64) = false := by
  rw [ProofLib.conditionHolds_eq_addsPState64]
  exact beq_eq_false_iff_ne.mpr hne

@[simp, arm64_norm]
abbrev leafSetUnackKyberPreKeyIdName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id"

/-- Specification of `<SessionState>::set_unacknowledged_kyber_pre_key_id`. -/
def leafSetUnackKyberPreKeyIdSpec : Spec (BitVec 64 × BitVec 64 × BitVec 32) where
  pre := fun (statePtr, cap, kyberPreKeyId) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ (s.readReg64 .x1).setWidth 32 = kyberPreKeyId ∧
      cap + 1#64 ≠ 0#64⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ cap) ∗
      (∃∗ w : BitVec 32, (statePtr + 0x140#64) ↦₃₂ w)
  post := fun (statePtr, cap, kyberPreKeyId) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ cap) ∗
      ((statePtr + 0x140#64) ↦₃₂ kyberPreKeyId)

theorem setUnackKyberId_ext_ok {b : BitVec 64} {extP : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b extP)
      ((tripleRatchetProgAtExt b extP).fnAddr leafSetUnackKyberPreKeyIdName)
      leafSetUnackKyberPreKeyIdSpec := by
  unfold leafSetUnackKyberPreKeyIdSpec
  code_fetches_range CryptoVerification.libsignalSessionCode Pqxdh.setUnackKyberPreKeyId b
    (Rust.withPanics extP)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id")
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_kyber_pre_key_id")) 0 52
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨statePtr, cap, kyberPreKeyId⟩
  dsimp only at *
  subst h_1 h_2
  wp_pull_exists
  have hcond : ConditionHolds .EQ (addsPState64 cap 1#64) = false :=
    cond_eq_adds_1_false_ext ‹_›
  wp_steps
  wp_done

@[simp, arm64_norm]
abbrev leafSetKyberCiphertextName : String :=
  "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext"

/-- Specification of `<SessionState>::set_kyber_ciphertext` on an empty slot (`0xffffffffffffffff`). -/
def leafSetKyberCiphertextNoneSpec : Spec (BitVec 64 × BitVec 64 × BitVec 64) where
  pre := fun (statePtr, ctPtr, ctLen) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ s.readReg64 .x1 = ctPtr ∧ s.readReg64 .x2 = ctLen⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w1 : BitVec 64, (statePtr + 0x130#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (statePtr + 0x138#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 32, (statePtr + 0x140#64) ↦₃₂ w3) ∗
      cells (s.sp - 48#64) 6
  post := fun (statePtr, ctPtr, ctLen) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((statePtr + 0x128#64) ↦₆₄ ctLen) ∗
      ((statePtr + 0x130#64) ↦₆₄ ctPtr) ∗
      ((statePtr + 0x138#64) ↦₆₄ ctLen) ∗
      ((statePtr + 0x140#64) ↦₃₂ 0xffffffff#32) ∗
      cells (s0.sp - 48#64) 6

theorem setKyberCiphertext_ext_ok {b : BitVec 64} {extP : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b extP)
      ((tripleRatchetProgAtExt b extP).fnAddr leafSetKyberCiphertextName)
      leafSetKyberCiphertextNoneSpec := by
  unfold leafSetKyberCiphertextNoneSpec
  cells_unfold
  code_fetches_range CryptoVerification.libsignalSessionCode Pqxdh.setKyberCiphertext b
    (Rust.withPanics extP)
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext")
    (num% (ls_off% "<libsignal_protocol::state::session::SessionState>::set_kyber_ciphertext")) 0 88
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  rcases x with ⟨statePtr, ctPtr, ctLen⟩
  dsimp only at *
  subst h h_1 h_2
  wp_pull_exists
  wp_steps
  wp_done

/-! ## `SessionState` builders and `derive_public_key_bytes` -/

theorem sessionStateNew_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Pqxdh.Initiator.sessionStateNewSym)
      (Pqxdh.Initiator.sessionStateNewSpec A img) :=
  Pqxdh.Initiator.sessionStateNew_base_ok_ext
    (Pqxdh.Initiator.SessionMemHooks.of_externsOk_cliExternsWith hOk)

theorem withReceiverChain_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Pqxdh.Initiator.withReceiverChainSym)
      (Pqxdh.Initiator.withReceiverChainEmptySpec A img) :=
  Pqxdh.Initiator.withReceiverChain_empty_base_ok_ext
    (Pqxdh.Initiator.SessionMemHooks.of_externsOk_cliExternsWith hOk)

theorem withSenderChain_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Pqxdh.Initiator.withSenderChainSym)
      (Pqxdh.Initiator.withSenderChainNoneSpec A img) :=
  Pqxdh.Initiator.withSenderChain_none_base_ok_ext
    (Pqxdh.Initiator.SessionMemHooks.of_externsOk_cliExternsWith hOk)

private theorem hookSat_cliExternsWith_local {α : Type} {ext : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (hnp : E2E.isImagePanicSymbol name = false)
    (h : HookSat ext name spec) :
    HookSat (cliExternsWith ext) name spec := by
  simp only [HookSat, cliExternsWith, withCliPanics_of_isImagePanicSymbol_false _ hnp]
  exact h

set_option maxRecDepth 2000000 in
theorem derivePubKeyBytes_ext_ok {b : BitVec 64} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr derivePublicKeyBytesName)
      (derivePublicKeyBytesStackSpec P.C.pubKey extHookStack) := by
  have hpub_fnOff : libsignalSessionCode.fnOff pubFromSecretName =
      num% (ls_off% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from") :=
    ls_stub% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"
  have hpub_raw : subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr pubFromSecretName)
      (CliExt.pubFromSecretSpec P.C) := by
    have h1 := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := cliExternsWith ext)
      (hname := pubFromSecretName) (k := 0) hpub_fnOff (Nat.add_zero _) (by decide)
      (ls_hook% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from")
      (by rfl_kernel) (hookSat_cliExternsWith_local (by rfl_kernel) hOk.pubFromSecret)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1
  refine derive_public_key_bytes_ok_of_contract_stack extHookStack (subroutine_ok_outcome_intro ?_)
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (CliExt.pubFromSecretSpec P.C).pre (x.secret, x.sec, x.out) s0 ∗ R := by
    dsimp only [CliExt.pubFromSecretSpec, CliExt.withStack, derivePublicKeyBytesStackSpec] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine (hpub_raw.to_outcome (x.secret, x.sec, x.out) R s0 hpc hrun hpre' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CliExt.pubFromSecretSpec, CliExt.withStack, derivePublicKeyBytesStackSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem derivePubKeyBytes_inImage_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr derivePublicKeyBytesName)
      ((derivePublicKeyBytesStackSpec P.C.pubKey extHookStack).inImage img) :=
  subroutine_ok_inImage_of_subroutine_ok img (derivePubKeyBytes_ext_ok hOk)

/-! ## `<kem::Ciphertext>::serialize` -/

private theorem stackAt_kemSerialize48_ext (sp : BitVec 64) :
    stackAt sp tryCloneFromRefStackX =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 := by
  simp only [stackAt, tryCloneFromRefStackX, extHookStack]
  have hsub : sp - 48#64 - BitVec.ofNat 64 (2 ^ 14) = sp - BitVec.ofNat 64 (2 ^ 14 + 48) := by
    bv_omega
  rw [hsub,
      ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 (2 ^ 14 + 48))
        (n := 2 ^ 14) (k := 48) (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      (ProofLib.memRegion_cells (sp - 48#64) 6 (by decide) :
        memRegion (sp - 48#64) 48 = cells (sp - 48#64) 6)]

private theorem memRegion_1569_split_ext (p : BitVec 64) :
    memRegion p 1569 = (∃∗ b0 : BitVec 8, p ↦₈ b0) ∗ memRegion (p + 1#64) 1568 := by
  rw [show (1569 : Nat) = 1 + 1568 by decide,
      memRegion_split p 1 1568 (by decide),
      memRegion_one p]

private theorem sepWPp_pure_mid_ext {prog : Program} {ret : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post postP : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (A ∗ B ∗ C) post postP) :
    SepWPp prog ret s (A ∗ B ∗ ⌜φ⌝ ∗ C) post postP := by
  rw [show A ∗ B ∗ ⌜φ⌝ ∗ C = ⌜φ⌝ ∗ A ∗ B ∗ C by ac_rfl]
  exact SepWPp.pure_elim h

private theorem hookOk_map_local {α β : Type} {f : State → State} {s₁ : Spec α} {s₂ : Spec β}
    (g : β → α) (I : State → State → Prop) (hI : ∀ s, I s (f s))
    (hh : HookOk f s₁)
    (hpre : ∀ y R s0, s0.mem ⊨ s₂.pre y s0 ∗ R → s0.mem ⊨ s₁.pre (g y) s0 ∗ R)
    (hpost : ∀ y R s0 sf, I s0 sf → s0.mem ⊨ s₂.pre y s0 ∗ R →
      sf.mem ⊨ s₁.post (g y) s0 sf ∗ R → sf.mem ⊨ s₂.post y s0 sf ∗ R)
    (hpanic : ∀ y R s0 sf, sf.mem ⊨ s₁.onPanic (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onPanic y s0 sf ∗ R)
    (hexit : ∀ y c R s0 sf,
      sf.mem ⊨ s₁.onExit (g y) c s0 sf ∗ R → sf.mem ⊨ s₂.onExit y c s0 sf ∗ R)
    (hoom : ∀ y R s0 sf, sf.mem ⊨ s₁.onOom (g y) s0 sf ∗ R → sf.mem ⊨ s₂.onOom y s0 sf ∗ R) :
    HookOk f s₂ := by
  intro y R s0 hrun hpreY hsp
  obtain ⟨hkf, hsym, hout⟩ := hh (g y) R s0 hrun (hpre y R s0 hpreY) hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hp1, hp2⟩ | ⟨c, he1, he2⟩ | ⟨ho1, ho2⟩
  · exact Or.inl ⟨hret, hcc, hpost y R s0 (f s0) (hI s0) hpreY hq⟩
  · exact Or.inr (Or.inl ⟨hp1, hpanic y R s0 (f s0) hp2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he1, hexit y c R s0 (f s0) he2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho1, hoom y R s0 (f s0) ho2⟩))

private theorem hookSat_map_local {α β : Type} {ext : String → Option (State → State)} {n : String}
    {s₁ : Spec α} {s₂ : Spec β} (hs : HookSat ext n s₁)
    (hm : ∀ f, HookOk f s₁ → HookOk f s₂) : HookSat ext n s₂ := by
  obtain ⟨f, hf, hok⟩ := hs
  exact ⟨f, hf, hm f hok⟩

private theorem hookOk_withStack_local {α : Type} {f : State → State} {base : Spec α}
    (hh : HookOk f base) (stk : Nat)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (LibsignalTripleRatchet.withStack base stk) := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ base.pre x s0 ∗ (stackAt s0.sp stk ∗ R) := by
    dsimp only [LibsignalTripleRatchet.withStack] at hpre
    rwa [sepConj_assoc] at hpre
  obtain ⟨hkf, hsym, hout⟩ := hh x (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalTripleRatchet.withStack]
    rwa [← sepConj_assoc] at hpost
  · rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he; exact False.elim he.1
  · rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho; exact False.elim ho.1

private theorem hookOk_stack_mono_local {α : Type} {f : State → State} {base : Spec α}
    {s1 s2 : Nat} (hh : HookOk f (LibsignalTripleRatchet.withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    HookOk f (LibsignalTripleRatchet.withStack base s2) := by
  intro x R s0 hrun hpre hsp
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (LibsignalTripleRatchet.withStack base s1).pre x s0 ∗ R' := by
    dsimp only [LibsignalTripleRatchet.withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hh x R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalTripleRatchet.withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [LibsignalTripleRatchet.withStack] at hp
    rw [hpan x s0 (f s0), satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [LibsignalTripleRatchet.withStack] at he
    rw [hex x code s0 (f s0), satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [LibsignalTripleRatchet.withStack] at ho
    rw [hoom x s0 (f s0), satisfies_pure_sepConj] at ho
    exact False.elim ho.1

private theorem hookOk_sessionMemcpy_of_cliExt_local {f : State → State} {stk : Nat}
    (hh : HookOk f CliExt.memcpySpec) (hle : CliExt.memHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    HookOk f (sessionMemcpySpec stk) := by
  have h1 : HookOk f (LibsignalTripleRatchet.withStack sessionMemcpyRegionSpec CliExt.memHookStack) :=
    hookOk_map_local (fun x => x) (fun _ _ => True) (fun _ => trivial) hh
      (fun _ _ _ hp => by simpa only [CliExt.memcpySpec, libcMemcpySpec,
        LibsignalTripleRatchet.withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
        sepConj_assoc] using hp)
      (fun _ _ _ _ _ _ hq => by simpa only [CliExt.memcpySpec, LibsignalTripleRatchet.withStack,
        sessionMemcpyRegionSpec, sepConj_assoc] using hq)
      (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)
  have h2 := hookOk_stack_mono_local h1 hle hmax
  exact hookOk_map_local (fun x => x) (fun _ _ => True) (fun _ => trivial) h2
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec,
      LibsignalTripleRatchet.withStack, sessionMemcpyRegionSpec, memcpyRegionSpec,
      sepConj_assoc] using hp)
    (fun _ _ _ _ _ _ hq => by simpa only [sessionMemcpySpec, LibsignalTripleRatchet.withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)
    (fun _ _ _ _ hq => hq) (fun _ _ _ _ _ hq => hq) (fun _ _ _ _ hq => hq)

theorem kemCtSerialize_ext_ok {b : BitVec 64} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt b (cliExternsWith ext))
      ((tripleRatchetProgAtExt b (cliExternsWith ext)).fnAddr Pqxdh.kemCiphertextSerializeName)
      (kemCiphertextSerializeExtSpec A) := by
  unfold kemCiphertextSerializeExtSpec
  simp only [stackAt_kemSerialize48_ext]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff Pqxdh.kemCiphertextSerializeName =
      num% (ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize") :=
    ls_lemma% fnOff "<libsignal_protocol::kem::Ciphertext>::serialize"
  have hshimSat : HookSat (cliExternsWith ext) "__rustc::__rust_no_alloc_shim_is_unstable_v2"
      (LibsignalTripleRatchet.withStack noAllocShimSpec extHookStack) :=
    hookSat_cliExternsWith_local (by rfl_kernel)
      (hookSat_map_local hOk.shim fun _ hh =>
        hookOk_withStack_local hh extHookStack)
  have hshim := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := cliExternsWith ext)
    (name := Pqxdh.kemCiphertextSerializeName)
    (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    hfn (by decide) (by decide)
    (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by rfl_kernel) hshimSat
  have halloc0 := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := cliExternsWith ext)
    (name := Pqxdh.kemCiphertextSerializeName)
    (hname := "__rustc::__rust_alloc")
    (k := num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    hfn (by decide) (by decide)
    (ls_hook% "__rustc::__rust_alloc") (by rfl_kernel)
    (hookSat_cliExternsWith_local (by rfl_kernel) hOk.alloc.alloc)
  have halloc : subroutine_ok (libsignalSessionCode.rebase b (Rust.withPanics (cliExternsWith ext)))
      ((libsignalSessionCode.rebase b (Rust.withPanics (cliExternsWith ext))).fnAddr
        Pqxdh.kemCiphertextSerializeName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize")))
      (rustAllocSpecWithStack A extHookStack) :=
    rustAllocWithStack_of_rustAlloc halloc0
  have hmcSat : HookSat (cliExternsWith ext) "memcpy" (sessionMemcpySpec extHookStack) :=
    hookSat_cliExternsWith_local (by rfl_kernel)
      (hookSat_map_local hOk.memcpy fun _ hh =>
        hookOk_sessionMemcpy_of_cliExt_local hh (by decide) (by decide))
  have hmemcpy := hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := cliExternsWith ext)
    (name := Pqxdh.kemCiphertextSerializeName)
    (hname := "memcpy")
    (k := num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    hfn (by decide) (by decide)
    (ls_hook% "memcpy") (by rfl_kernel) hmcSat
  have hpanic := panic_at_panicSymbol (P := libsignalSessionCode) (b := b)
    (hooks := cliExternsWith ext) (name := Pqxdh.kemCiphertextSerializeName)
    (hname := "alloc::raw_vec::handle_error")
    (k := num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize"))
    hfn (by decide) (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by rfl_kernel)
  dsimp only [LibsignalTripleRatchet.withStack, noAllocShimSpec] at hshim
  dsimp only [rustAllocSpecWithStack] at halloc
  dsimp only [sessionMemcpySpec] at hmemcpy
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.kemCiphertextSerialize b
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize")) 0 144
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmemcpy hpanic ⊢
  clear hfn hOk hshimSat halloc0 hmcSat
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (cliExternsWith ext))).fnAddr Pqxdh.kemCiphertextSerializeName = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (cliExternsWith ext))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init g s0
  obtain ⟨hdrPtr, boxPtr, ctBytes⟩ := g
  dsimp only at *
  subst h_1
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 1569 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 72#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (1569, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid_ext fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry +
      BitVec.ofNat 64 (num% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<libsignal_protocol::kem::Ciphertext>::serialize")))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_1569_split_ext, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid_ext fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← h]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5) + 1#64, boxPtr, ctBytes)
    wp_steps
    simp only [pointsToBytes_cons]
    wp_done

/-! ## `<SessionRecord>::promote_state` -/

section PromoteStateExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1200000 in
private theorem archive_current_state_inner_empty_ext_ok {b : BitVec 64}
    {extP : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b extP)
      ((tripleRatchetProgAtExt b extP).fnAddr Pqxdh.ResponderStore.archiveCurrentStateInnerName)
      Pqxdh.ResponderStore.archiveCurrentStateInnerEmptySpec := by
  unfold Pqxdh.ResponderStore.archiveCurrentStateInnerEmptySpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff Pqxdh.ResponderStore.archiveCurrentStateInnerName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") :=
    ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.ResponderStore.responderBin b
    (Rust.withPanics extP) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")) 0 412
  wp_init recPtr s0
  examples_generalize_entry
  examples_hide_fetches
  subst h
  wp_steps
  wp_done

private theorem stackAt_promoteState_ext_split (sp : BitVec 64) :
    stackAt sp (extHookStack + 32) =
      memRegion (sp - 16416#64) 16320 ∗
      cells (sp - 96#64) 8 ∗
      cells (sp - 32#64) 4 := by
  simp only [stackAt, extHookStack]
  rw [show (2 ^ 14 + 32 : Nat) = 16416 from rfl,
      show BitVec.ofNat 64 16416 = 16416#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 16416#64) (n := 16320) (k := 96)
        (b' := sp - 96#64) (by decide) (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 64) (k := 32)
        (b' := sp - 32#64) (by decide) (by bv_omega) (by decide),
      (ProofLib.memRegion_cells (sp - 96#64) 8 (by decide) :
        memRegion (sp - 96#64) 64 = cells (sp - 96#64) 8),
      (ProofLib.memRegion_cells (sp - 32#64) 4 (by decide) :
        memRegion (sp - 32#64) 32 = cells (sp - 32#64) 4)]

private theorem stackAt_promoteState_tail_merge (sp : BitVec 64) :
    memRegion (sp - 16416#64) 16320 ∗ cells (sp - 96#64) 8 ∗ cells (sp - 32#64) 4 =
      memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [← stackAt_promoteState_ext_split sp]
  simp only [stackAt, extHookStack]
  rw [show (2 ^ 14 + 32 : Nat) = 16416 from rfl,
      show (2 ^ 14 : Nat) = 16384 from rfl,
      show BitVec.ofNat 64 16416 = 16416#64 from rfl,
      show BitVec.ofNat 64 16384 = 16384#64 from rfl]
  exact ProofLib.memRegion_split' (b := sp - 16416#64) (n := 32) (k := 16384)
    (b' := sp - 16384#64) (by decide) (by bv_omega) (by decide)

private theorem cells_sub32_4_merge_ext (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1200000 in
theorem promoteState_ext_ok {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base (cliExternsWith ext))
      ((tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr Pqxdh.ResponderStore.promoteStateName)
      (promoteStateEmptyExtSpec img (extHookStack + 32)) := by
  unfold promoteStateEmptyExtSpec
  have hfn : libsignalSessionCode.fnOff Pqxdh.ResponderStore.promoteStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") :=
    ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_state"
  have harch := archive_current_state_inner_empty_ext_ok (b := img.base) (extP := cliExternsWith ext)
  have hrel : (tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        Pqxdh.ResponderStore.archiveCurrentStateInnerName =
      (tripleRatchetProgAtExt img.base (cliExternsWith ext)).fnAddr
        Pqxdh.ResponderStore.promoteStateName + 2804#64 := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, hfn,
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner"),
      BitVec.add_assoc]
    rfl
  rw [hrel] at harch
  clear hrel
  have hmcSat : HookSat (cliExternsWith ext) "memcpy" (sessionMemcpySpec extHookStack) :=
    hookSat_cliExternsWith_local (by rfl_kernel)
      (hookSat_map_local hOk.memcpy fun _ hh =>
        hookOk_sessionMemcpy_of_cliExt_local hh (by decide) (by decide))
  have hmemcpy := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (name := Pqxdh.ResponderStore.promoteStateName)
    (hname := "memcpy")
    (k := num% (ls_off% "memcpy" -
      ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
    hfn (by decide) (by decide)
    (ls_hook% "memcpy") (by rfl_kernel) hmcSat
  dsimp only [sessionMemcpySpec] at hmemcpy
  code_fetches_range CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.ResponderStore.responderBin img.base
    (Rust.withPanics (cliExternsWith ext)) hfn
    (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state")) 0 68
  wp_init x s0
  dsimp only [tripleRatchetProgAtExt] at harch hmemcpy ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, srcPtr, bs⟩ := x
  dsimp only at *
  subst h_2 h_3
  have hc4 : cells (s0.sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
        ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  conv => arg 4; rw [stackAt_promoteState_ext_split s0.sp, hc4]
  simp only [sepExists_sepConj_right]
  wp_pull_exists
  wp_steps
  have hsp_sub : s0.sp - 32#64 - 64#64 = s0.sp - 96#64 := by bv_arith
  wp_call harch (s0.readReg64 (.gpr 0#5))
  wp_steps
  apply SepWP.replace_pre (by sep_focus)
    (Pqxdh.ResponderStore.pointsTo64_memRegion_336_entails_344
      (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
  apply SepWP.replace_pre (by sep_focus)
    (cells_sub32_4_merge_ext s0.sp _ _ _ _)
  have htail := stackAt_promoteState_tail_merge s0.sp
  have hpre_eq :
      cells (s0.sp - 32#64) 4 ∗
      memRegion (s0.readReg64 (.gpr 0#5) + 24#64) 344 ∗
      cells (s0.sp - 96#64) 8 ∗
      (s0.readReg64 (.gpr 1#5) ↦ₛ bs) ∗
      memRegion (s0.sp - 16416#64) 16320 =
      memRegion (s0.readReg64 (.gpr 0#5) + 0x18#64) bs.length ∗
      (s0.readReg64 (.gpr 1#5) ↦ₛ bs) ∗
      stackAt s0.sp extHookStack ∗
      memRegion (s0.sp - 16416#64) 32 := by
    rw [h]
    trans ((memRegion (s0.sp - 16416#64) 16320 ∗ cells (s0.sp - 96#64) 8 ∗ cells (s0.sp - 32#64) 4) ∗
      (memRegion (s0.readReg64 (.gpr 0#5) + 24#64) 344 ∗ (s0.readReg64 (.gpr 1#5) ↦ₛ bs)))
    · ac_rfl
    · rw [htail]; ac_rfl
  conv => arg 4; rw [hpre_eq]
  wp_call hmemcpy (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
  conv => arg 4; rw [show
    ((s0.readReg64 (.gpr 0#5) + 24#64) ↦ₛ bs) ∗ (s0.readReg64 (.gpr 1#5) ↦ₛ bs) ∗
      stackAt s0.sp extHookStack ∗ memRegion (s0.sp - 16416#64) 32 =
    ((s0.readReg64 (.gpr 0#5) + 24#64) ↦ₛ bs) ∗ (s0.readReg64 (.gpr 1#5) ↦ₛ bs) ∗
      (memRegion (s0.sp - 16416#64) 32 ∗ stackAt s0.sp extHookStack) by ac_rfl,
    ← htail, ← stackAt_promoteState_ext_split s0.sp]
  wp_done

end PromoteStateExt

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
