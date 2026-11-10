/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKit
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentitySpec
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SelfRel
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdKeyPairVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdRegIdVtables
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.DecryptPrekeySlot
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import ProofLib.SpecAudit

/-!
# CLI Self-Identity Store Specification

Instantiates `IdentitySelfStoreSpec` (`cliIdentitySelfSpec`) over `cliIdentityStoreSpec` for
`<IdentityFiles as IdentityKeyStore>::get_identity_key_pair` and `get_local_registration_id`,
defining the 48-byte `SignalProtocolError` layout `cliSelfSpeErrSpec` (`RunDrop.SpeOwned`),
establishing `IdentitySelfVtablesOk`, and proving answer totality and sret layout bi-entailments.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst.SelfRel

/-! ## Future-box deallocation bridge -/

section BoxBridge

private theorem pointsTo64_eq_bytes8 (a w : BitVec 64) :
    (a ↦₆₄ w) =
      (a ↦ₛ [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
              w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8]) := by
  simp only [pointsTo64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero, BitVec.add_assoc]
  rfl

/-- Any 16-byte self-identity future box (`idOwnFutBoxAt`) entails raw `memRegion box 16`. -/
theorem idOwnFutBoxAt_memRegion (box self : BitVec 64) (st : BitVec 8) :
    idOwnFutBoxAt box self st ⊢ memRegion box 16 := by
  unfold idOwnFutBoxAt
  have h9 : (box + 8#64) + 1#64 = box + 9#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [memRegion_split box 8 8 (by decide),
    memRegion_split (box + 8#64) 1 7 (by decide), h9]
  have hw0 : (box ↦₆₄ self) ⊢ memRegion box 8 := by
    rw [pointsTo64_eq_bytes8]
    exact ProofLib.pointsToBytes_entails_memRegion box _
  have hw8 : ((box + 8#64) ↦₈ st) ⊢ memRegion (box + 8#64) 1 := by
    have hb1 : ((box + 8#64) ↦₈ st) = ((box + 8#64) ↦ₛ [st]) := by
      simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
    rw [hb1]
    exact ProofLib.pointsToBytes_entails_memRegion (box + 8#64) [st]
  exact sepConj_mono hw0 (sepConj_mono hw8 (Entails.refl _))

end BoxBridge

/-! ## `SignalProtocolError` witness and `RunDrop.speOwnedAt` equivalence -/

/-- Witness carrying a `RunDrop.SpeOwned` error variant, its 6 sret words, and the 3 niche-tag
non-equalities required by `SpeErrSpec`. -/
structure CliSelfSpeErr where
  k : RunDrop.SpeOwned
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64
  w0_ne_err : w0 ≠ errTag
  w0_ne_ok : w0 ≠ okTagVec
  w0_ne_pending : w0 ≠ 0xFFFFFFFFFFFFFFFD#64

/-- Explicit inhabitant of `CliSelfSpeErr` (`BadKemKeyType`, `speWord 31`). -/
def cliSelfSpeErrWitness : CliSelfSpeErr where
  k := .badKemKeyType
  w0 := speWord 31
  w1 := 0#64
  w2 := 0#64
  w3 := 0#64
  w4 := 0#64
  w5 := 0#64
  w0_ne_err := by decide
  w0_ne_ok := by decide
  w0_ne_pending := by decide

instance : Inhabited CliSelfSpeErr := ⟨cliSelfSpeErrWitness⟩
instance : Nonempty CliSelfSpeErr := ⟨cliSelfSpeErrWitness⟩

/-- 48-byte `SpeErrSpec` backed by `RunCompose.dpErrHeap`. -/
def cliSelfSpeErrSpec (A : RustAlloc) : SpeErrSpec CliSelfSpeErr where
  w0 := CliSelfSpeErr.w0
  w1 := CliSelfSpeErr.w1
  w2 := CliSelfSpeErr.w2
  w3 := CliSelfSpeErr.w3
  w4 := CliSelfSpeErr.w4
  w5 := CliSelfSpeErr.w5
  heap := fun e => dpErrHeap A [e.w0, e.w1, e.w2, e.w3, e.w4, e.w5] e.k
  w0_ne_err := CliSelfSpeErr.w0_ne_err
  w0_ne_ok := CliSelfSpeErr.w0_ne_ok
  w0_ne_pending := CliSelfSpeErr.w0_ne_pending

section SpeErrBridge

private theorem sepConj_pure_of_true (P : SepProp) {φ : Prop} (hφ : φ) : P ∗ ⌜φ⌝ = P := by
  have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [hEq, pure_true, sepConj_emp]

private theorem pure_sepConj_eq_of_true {φ : Prop} (P : SepProp) (hφ : φ) : ⌜φ⌝ ∗ P = P := by
  rw [sepConj_comm, sepConj_pure_of_true P hφ]

private theorem ent_pure_right {φ : Prop} (hφ : φ) {P Q : SepProp} (h : P ⊢ Q) : P ⊢ ⌜φ⌝ ∗ Q := by
  rw [pure_sepConj_eq_of_true Q hφ]
  exact h

private theorem ent_pure_peek {φ : Prop} {P Q : SepProp}
    (h : φ → (⌜φ⌝ ∗ P ⊢ Q)) : ⌜φ⌝ ∗ P ⊢ Q :=
  Entails.pure_left fun hφ => by
    rw [← pure_sepConj_eq_of_true P hφ]
    exact h hφ

private theorem ent_pure_peek_only {φ ψ : Prop} (h : φ → ψ) : ⌜φ⌝ ⊢ ⌜ψ⌝ ∗ ⌜φ⌝ :=
  Entails.pure_left_only fun hφ => by
    have hEq : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
    rw [hEq, pure_true]
    exact ent_pure_right (h hφ) (Entails.refl _)

private theorem speWordsAt_eq_dpWordsAt (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    speWordsAt a w0 w1 w2 w3 w4 w5 = dpWordsAt a [w0, w1, w2, w3, w4, w5] := by
  dsimp only [speWordsAt, dpWordsAt]
  have h16 : (a + 8#64) + 8#64 = a + 16#64 := by rw [BitVec.add_assoc]; rfl
  have h24 : (a + 16#64) + 8#64 = a + 24#64 := by rw [BitVec.add_assoc]; rfl
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have h40 : (a + 32#64) + 8#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
  rw [h16, h24, h32, h40, sepConj_emp]

private theorem plainSpeTag_ne_tags {i : Nat} (hi : RunDrop.PlainSpeTag i) :
    speWord i ≠ errTag ∧ speWord i ≠ okTagVec ∧ speWord i ≠ 0xFFFFFFFFFFFFFFFD#64 := by
  unfold RunDrop.PlainSpeTag RunDrop.plainSpeTags at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem strSpeTag_ne_tags {i : Nat} (hi : RunDrop.StrSpeTag i) :
    speWord i ≠ errTag ∧ speWord i ≠ okTagVec ∧ speWord i ≠ 0xFFFFFFFFFFFFFFFD#64 := by
  unfold RunDrop.StrSpeTag RunDrop.strSpeTags at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem cap_lt_half_ne_tags {cap : BitVec 64} (hcap : cap.toNat < 2 ^ 63) :
    cap ≠ errTag ∧ cap ≠ okTagVec ∧ cap ≠ 0xFFFFFFFFFFFFFFFD#64 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro heq <;> subst heq
  · have h1 : errTag.toNat = 2 ^ 64 - 1 := by decide
    omega
  · have h2 : okTagVec.toNat = 2 ^ 64 - 2 := by decide
    omega
  · have h3 : (0xFFFFFFFFFFFFFFFD#64 : BitVec 64).toNat = 2 ^ 64 - 3 := by decide
    omega

/-- Every `RunDrop.SpeOwned` variant's `dpErrHeap` forces word 0 away from `errTag` (`-1`),
`okTagVec` (`-2`), and `pendingTag` (`-3`). -/
theorem dpErrHeap_w0_ne_tags (A : RustAlloc) (w0 w1 w2 w3 w4 w5 : BitVec 64)
    (k : RunDrop.SpeOwned) :
    dpErrHeap A [w0, w1, w2, w3, w4, w5] k ⊢
      ⌜w0 ≠ errTag ∧ w0 ≠ okTagVec ∧ w0 ≠ 0xFFFFFFFFFFFFFFFD#64⌝ ∗
        dpErrHeap A [w0, w1, w2, w3, w4, w5] k := by
  cases k with
  | badKemKeyType =>
    dsimp only [dpErrHeap]
    exact ent_pure_peek_only fun hw0 => by subst hw0; decide
  | badKemKeyLength =>
    dsimp only [dpErrHeap]
    exact ent_pure_peek_only fun hw0 => by subst hw0; decide
  | plain i hi =>
    dsimp only [dpErrHeap]
    exact ent_pure_peek_only fun hw0 => by subst hw0; exact plainSpeTag_ne_tags hi
  | withString i hi =>
    dsimp only [dpErrHeap]
    exact ent_pure_peek fun hw0 => by
      subst hw0
      exact ent_pure_right (strSpeTag_ne_tags hi) (Entails.refl _)
  | untrustedIdentity _ =>
    dsimp only [dpErrHeap]
    exact ent_pure_peek fun ⟨hw0, _, _⟩ => by
      subst hw0
      exact ent_pure_right (by decide) (Entails.refl _)
  | sessionNotFound addr op =>
    dsimp only [dpErrHeap, vecU8Heap]
    have hassoc :
        ⌜w2 = BitVec.ofNat 64 addr.name.length ∧ w3.extractLsb' 0 8 = addr.device⌝ ∗
          (⌜addr.name.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
            (if w0 = 0 then emp
             else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ addr.name) ∗
               memRegion (w1 + BitVec.ofNat 64 addr.name.length) (w0.toNat - addr.name.length))) ∗
          strRefHeap w4 w5 (LibsignalTripleRatchetRepr.utf8 op) =
        ⌜addr.name.length ≤ w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0⌝ ∗
          (⌜w2 = BitVec.ofNat 64 addr.name.length ∧ w3.extractLsb' 0 8 = addr.device⌝ ∗
            (if w0 = 0 then emp
             else A.live w1 w0.toNat 1 ∗ (w1 ↦ₛ addr.name) ∗
               memRegion (w1 + BitVec.ofNat 64 addr.name.length) (w0.toNat - addr.name.length)) ∗
            strRefHeap w4 w5 (LibsignalTripleRatchetRepr.utf8 op)) := by ac_rfl
    rw [hassoc]
    refine ent_pure_peek fun ⟨_, hcap, _⟩ => ?_
    rw [← hassoc]
    exact ent_pure_right (cap_lt_half_ne_tags hcap) (Entails.refl _)
  | proto fnName e =>
    cases e with
    | panic =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact Entails.pure_left_only False.elim
    | invalidState =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek fun hw0 => by
        subst hw0
        exact ent_pure_right (by decide) (Entails.refl _)
    | ciphertextMessageTooShort _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun ⟨hw0, _⟩ => by subst hw0; decide
    | legacyCiphertextVersion _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun ⟨hw0, _⟩ => by subst hw0; decide
    | unrecognizedCiphertextVersion _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun ⟨hw0, _⟩ => by subst hw0; decide
    | invalidProtobufEncoding =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun hw0 => by subst hw0; decide
    | noKeyTypeIdentifier =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun hw0 => by subst hw0; decide
    | badKeyType _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun ⟨hw0, _⟩ => by subst hw0; decide
    | badKeyLength _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun ⟨hw0, _⟩ => by subst hw0; decide
    | invalidKeyAgreement =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun hw0 => by subst hw0; decide
    | invalidSessionStructure _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek fun hw0 => by
        subst hw0
        exact ent_pure_right (by decide) (Entails.refl _)
    | duplicatedMessage _ _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek_only fun ⟨hw0, _⟩ => by subst hw0; decide
    | invalidMessage _ _ =>
      dsimp only [dpErrHeap, dpProtoHeap]
      exact ent_pure_peek fun ⟨hw0, _⟩ => by
        subst hw0
        exact ent_pure_right (by decide) (Entails.refl _)

/-- Two-sided equivalence between `∃∗ e : CliSelfSpeErr, speErrAt (cliSelfSpeErrSpec A) a e`
and `∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k`. -/
theorem cliSelfSpeErrAt_biEntails (A : RustAlloc) (a : BitVec 64) :
    ((∃∗ e : CliSelfSpeErr, speErrAt (cliSelfSpeErrSpec A) a e) ⊢
      (∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k)) ∧
    ((∃∗ k : RunDrop.SpeOwned, RunDrop.speOwnedAt A a k) ⊢
      (∃∗ e : CliSelfSpeErr, speErrAt (cliSelfSpeErrSpec A) a e)) := by
  constructor
  · refine Entails.sepExists_elim fun e => ?_
    dsimp only [speErrAt, cliSelfSpeErrSpec]
    rw [speWordsAt_eq_dpWordsAt]
    exact Entails.trans (dpWords_errHeap_entails_speOwnedAt A a
      [e.w0, e.w1, e.w2, e.w3, e.w4, e.w5] e.k)
      (Entails.sepExists_right e.k (Entails.refl _))
  · refine Entails.sepExists_elim fun k => ?_
    refine Entails.trans (speOwnedAt_entails_dpWords_errHeap A a k) ?_
    refine Entails.sepExists_elim fun ws => ?_
    refine Entails.pure_left fun ⟨hlen, _⟩ => ?_
    rcases ws with _ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | _⟩⟩⟩⟩⟩⟩ <;>
      try (simp at hlen)
    refine Entails.trans (sepConj_mono_right (dpErrHeap_w0_ne_tags A w0 w1 w2 w3 w4 w5 k)) ?_
    have hpull :
        dpWordsAt a [w0, w1, w2, w3, w4, w5] ∗
          (⌜w0 ≠ errTag ∧ w0 ≠ okTagVec ∧ w0 ≠ 0xFFFFFFFFFFFFFFFD#64⌝ ∗
            dpErrHeap A [w0, w1, w2, w3, w4, w5] k) =
        ⌜w0 ≠ errTag ∧ w0 ≠ okTagVec ∧ w0 ≠ 0xFFFFFFFFFFFFFFFD#64⌝ ∗
          (dpWordsAt a [w0, w1, w2, w3, w4, w5] ∗ dpErrHeap A [w0, w1, w2, w3, w4, w5] k) := by
      ac_rfl
    rw [hpull]
    refine Entails.pure_left fun ⟨hne_err, hne_ok, hne_pending⟩ => ?_
    refine Entails.sepExists_right
      ⟨k, w0, w1, w2, w3, w4, w5, hne_err, hne_ok, hne_pending⟩ ?_
    dsimp only [speErrAt, cliSelfSpeErrSpec]
    rw [speWordsAt_eq_dpWordsAt]
    exact Entails.refl _

end SpeErrBridge

/-! ## `IdentitySelfStoreSpec` instance -/

/-- Concrete `IdentitySelfStoreSpec` for CLI `IdentityFiles` at peer `peer` and initial files `F0`. -/
def cliIdentitySelfSpec (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat}
    (kpShimStk kpPollStk regIdShimStk regIdPollStk : Nat) :
    IdentitySelfStoreSpec (cliIdentityStoreSpec A b rd F0 pathOk peer t1 t2 t3 t4) where
  fdsOk := fun fs => FdsGe3Closed fs
  KpErr := CliSelfSpeErr
  RegIdErr := CliSelfSpeErr
  kpErr := cliSelfSpeErrSpec A
  regIdErr := cliSelfSpeErrSpec A
  kpRel := cliKpRel rd F0
  regIdRel := cliRegIdRel rd F0
  kpEvs := fun _ => []
  regIdEvs := fun _ => []
  kpShimOff := cliIdKpShimOff
  kpFutVtOff := idKeyPairFutVtOff
  kpPollOff := cliIdKpPollOff
  kpFutDropOff := cliIdFutDropOff
  regIdShimOff := cliIdRegIdShimOff
  regIdFutVtOff := idRegIdFutVtOff
  regIdPollOff := cliIdRegIdPollOff
  regIdFutDropOff := cliIdFutDropOff
  kpBoxSize := 16
  regIdBoxSize := 16
  kpShimStack := kpShimStk
  kpPollStack := kpPollStk
  regIdShimStack := regIdShimStk
  regIdPollStack := regIdPollStk
  kpBoxAt := idOwnFutBoxAt
  regIdBoxAt := idOwnFutBoxAt
  kpBoxAt_memRegion := idOwnFutBoxAt_memRegion
  regIdBoxAt_memRegion := idOwnFutBoxAt_memRegion
  kpBoxSize_ne_zero := by decide
  regIdBoxSize_ne_zero := by decide
  kpBoxSize_lt := by decide
  regIdBoxSize_lt := by decide
  kpFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  regIdFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

/-! ## Vtable validity and quietness -/

section VtablesAndQuiet

variable {A : RustAlloc} {img : Obj.Image} {rd : ReadRule} {F0 : FsFiles}
  {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost}
  {t1 t2 t3 t4 k1 k2 k3 k4 : Nat}

/-- Vtable validity (`IdentitySelfVtablesOk`) for `cliIdentitySelfSpec`. -/
theorem cliIdSelfVtables_ok (himg : Obj.Loads libsignalSessionImage img) :
    IdentitySelfVtablesOk img
      (cliIdentityStoreSpec A img.base rd F0 pathOk peer t1 t2 t3 t4)
      (cliIdentitySelfSpec A img.base rd F0 pathOk peer k1 k2 k3 k4) where
  kpSlot := cliIdKpSlot_ok himg
  regIdSlot := cliIdRegIdSlot_ok himg
  kpFutDrop := cliIdKpFutDrop_ok himg
  kpFutSize := cliIdKpFutSize_ok himg
  kpFutAlign := cliIdKpFutAlign_ok himg
  kpFutPoll := cliIdKpFutPoll_ok himg
  regIdFutDrop := cliIdRegIdFutDrop_ok himg
  regIdFutSize := cliIdRegIdFutSize_ok himg
  regIdFutAlign := cliIdRegIdFutAlign_ok himg
  regIdFutPoll := cliIdRegIdFutPoll_ok himg

/-- `cliIdentitySelfSpec` emits no filesystem trace events (`Quiet`). -/
theorem cliIdentitySelfSpec_quiet :
    (cliIdentitySelfSpec A img.base rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).Quiet :=
  ⟨fun _ => by simp [cliIdentitySelfSpec, NoFsEv],
    fun _ => by simp [cliIdentitySelfSpec, NoFsEv]⟩

end VtablesAndQuiet

/-! ## Totality, relation equalities, and sret layout bi-entailments -/

section G4V2

instance cliIdentitySelf_kpErr_nonempty (A : RustAlloc) (b : BitVec 64) (rd : ReadRule)
    (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat} (k1 k2 k3 k4 : Nat) :
    Nonempty (cliIdentitySelfSpec A b rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).KpErr :=
  ⟨cliSelfSpeErrWitness⟩

instance cliIdentitySelf_regIdErr_nonempty (A : RustAlloc) (b : BitVec 64) (rd : ReadRule)
    (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop) (peer : AddrGhost)
    {t1 t2 t3 t4 : Nat} (k1 k2 k3 k4 : Nat) :
    Nonempty (cliIdentitySelfSpec A b rd F0 pathOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).RegIdErr :=
  ⟨cliSelfSpeErrWitness⟩

theorem cliIdentitySelf_kpRel_total {A : RustAlloc} {img : Obj.Image} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).kpRel g ans :=
  cliKpRel_total cliSelfSpeErrWitness cliIo.rd F0 g

theorem cliIdentitySelf_regIdRel_total {A : RustAlloc} {img : Obj.Image} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) (g : IdGhost) :
    ∃ ans,
      (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).regIdRel g ans :=
  cliRegIdRel_total cliSelfSpeErrWitness cliIo.rd F0 g

theorem cliIdentitySelf_kpRel_eq {A : RustAlloc} {img : Obj.Image} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) :
    (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).kpRel =
      cliKpRel cliIo.rd F0 :=
  rfl

theorem cliIdentitySelf_regIdRel_eq {A : RustAlloc} {img : Obj.Image} {peer : AddrGhost}
    {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (F0 : FsFiles) :
    (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
      (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4).regIdRel =
      cliRegIdRel cliIo.rd F0 :=
  rfl

/-- Two-sided `.error` layout bi-entailment between `kpPollOutAt` and `idKeyPairOutAt`. -/
theorem cliIdentitySelf_kpErr_layout (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles)
    {peer : AddrGhost} {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (out : BitVec 64) :
    ((∃∗ e, kpPollOutAt
      (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e)) ⊢
      idKeyPairOutAt A out (.error ())) ∧
    (idKeyPairOutAt A out (.error ()) ⊢
      (∃∗ e, kpPollOutAt
        (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
          (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e))) := by
  obtain ⟨hfwd, hrev⟩ := cliSelfSpeErrAt_biEntails A (out + 8#64)
  dsimp only [kpPollOutAt, idKeyPairOutAt, cliIdentitySelfSpec]
  constructor
  · refine Entails.sepExists_elim fun e => ?_
    have he : speErrAt (cliSelfSpeErrSpec A) (out + 8#64) e ⊢
        SepProp.sepExists fun k : RunDrop.SpeOwned => RunDrop.speOwnedAt A (out + 8#64) k :=
      Entails.trans (Entails.sepExists_right e (Entails.refl _)) hfwd
    exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
      (sepConj_mono he (Entails.refl _)))
  · have hpull :
        (out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗
          SepProp.sepExists (fun k : RunDrop.SpeOwned => RunDrop.speOwnedAt A (out + 8#64) k) ∗
          memRegion (out + 0x38#64) 16 =
        SepProp.sepExists (fun k : RunDrop.SpeOwned => RunDrop.speOwnedAt A (out + 8#64) k) ∗
          ((out ↦₈ 1#8) ∗ memRegion (out + 1#64) 7 ∗ memRegion (out + 0x38#64) 16) := by
      ac_rfl
    rw [hpull]
    refine Entails.trans (sepConj_mono_left hrev) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun e => ?_
    refine Entails.sepExists_right e ?_
    exact Entails.of_eq (by ac_rfl)

/-- Two-sided `.error` layout bi-entailment between `regIdPollOutAt` and `idRegIdOutAt`. -/
theorem cliIdentitySelf_regIdErr_layout (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles)
    {peer : AddrGhost} {t1 t2 t3 t4 k1 k2 k3 k4 : Nat} (out : BitVec 64) :
    ((∃∗ e, regIdPollOutAt
      (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
        (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e)) ⊢
      idRegIdOutAt A out (.error ())) ∧
    (idRegIdOutAt A out (.error ()) ⊢
      (∃∗ e, regIdPollOutAt
        (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
          (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4) out (.error e))) := by
  dsimp only [regIdPollOutAt, idRegIdOutAt, cliIdentitySelfSpec]
  exact cliSelfSpeErrAt_biEntails A out

#spec_nonvacuous! (fun (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost)
    (t1 t2 t3 t4 k1 k2 k3 k4 : Nat) =>
  kitKpShimSpec (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4))

#spec_nonvacuous! (fun (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost)
    (t1 t2 t3 t4 k1 k2 k3 k4 : Nat) =>
  kitRegIdShimSpec (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4))

#spec_nonvacuous! (fun (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost)
    (t1 t2 t3 t4 k1 k2 k3 k4 : Nat) =>
  kitKpPollSpecI img (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4))

#spec_nonvacuous! (fun (A : RustAlloc) (img : Obj.Image) (F0 : FsFiles) (peer : AddrGhost)
    (t1 t2 t3 t4 k1 k2 k3 k4 : Nat) =>
  kitRegIdPollSpecI img (cliIdentitySelfSpec A img.base cliIo.rd F0 cliWrOk peer
    (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) k1 k2 k3 k4))

end G4V2

end CryptoVerification.SignalSession.Cli.KitInst
