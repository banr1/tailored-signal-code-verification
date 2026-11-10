/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import LibsignalBinary.Proofs.ConsumeMessageKey.CanonKey
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.DeserializeLeaves
import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Fields
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push

@[expose] public section

set_option autoImplicit false

/-!
# Exact-to-Open `SessionRecord::deserialize` Specification Transport

Proves that `subroutine_ok prog entry deserializeExactSpec` implies `recordDeserializeOpenSpec`
generically over `prog`, `entry`, and `A : RustAlloc`, including relocatable `[LibsignalPlacement]`
transport under `LibsignalCodeRoLoaded`.
-/

namespace Proofs.libsignal.Hooks2

open Arm64 ProofLib SepProp CryptoVerification
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.Serialization
open CryptoVerification.E2E.Bin

theorem L1_DeserTransportX : True := trivial

/-- Exact-postcondition `SessionRecord::deserialize` contract (`deserOutRecordG` niche form),
parameterized by a loaded `img`. Pre = `deserializeGenSpecAt img`.pre. -/
noncomputable def deserializeExactSpecAtX (img : Obj.Image) : Spec DeserializeGenGhost where
  pre := (deserializeGenSpecAt img).pre
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ CryptoVerification.E2E.Record.encodeRecord x.r) ∗
      deserOutRecordG x.out x.r ∗
      stackAt s0.sp recDeserializeStack
  onPanic := (deserializeGenSpecAt img).onPanic

theorem stackAt_sub_splitX (sp : BitVec 64) (k m : Nat) (hkm : k ≤ m)
    (hm : m ≤ 2 ^ 64) :
    stackAt sp m =
      memRegion (sp - BitVec.ofNat 64 m) (m - k) ∗ stackAt sp k := by
  unfold stackAt
  have hsplit := memRegion_split' (b := sp - BitVec.ofNat 64 m) (b' := sp - BitVec.ofNat 64 k)
    (N := m) (n := m - k) (k := k) (by omega)
    (by
      have h1 : BitVec.ofNat 64 m = BitVec.ofNat 64 (m - k) + BitVec.ofNat 64 k := by
        rw [← BitVec.ofNat_add, Nat.sub_add_cancel hkm]
      rw [h1]
      bv_lin)
    (by omega)
  rw [hsplit]

theorem stackAt_recordDeserialize_splitX (sp : BitVec 64) :
    stackAt sp recordDeserializeStack =
      memRegion (sp - BitVec.ofNat 64 recordDeserializeStack)
        (recordDeserializeStack - recDeserializeStack) ∗
      stackAt sp recDeserializeStack :=
  stackAt_sub_splitX sp recDeserializeStack recordDeserializeStack (by decide) (by decide)

theorem mem_zip_of_mem_leftX :
    ∀ {α β : Type} {xs : List α} {ys : List β} {x : α},
      xs.length = ys.length → x ∈ xs → ∃ y, (x, y) ∈ xs.zip ys
  | _, _, [], [], _, _, hx => by simp at hx
  | _, _, x' :: xs, y' :: ys, x, hlen, hx => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨y', List.mem_cons_self ..⟩
    · obtain ⟨y, hy⟩ := mem_zip_of_mem_leftX hlen hx
      exact ⟨y, List.mem_cons_of_mem _ hy⟩

theorem binCanonSession_of_canonSessionX {G0 G : SessionGhost} {s : Session (List (BitVec 8))}
    (h0 : BinCanonSession G0 s) (hG : Serialization.CanonSession G s) :
    BinCanonSession G s := by
  rcases h0 with ⟨_, hwf, _, _, _, hrc_len, hrc_mk, _, halice, hkyber, hpq, henc⟩
  rcases hG with ⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩
  refine ⟨⟨hlocal, hrem, hsender, hlen_eq, hzip, hpend⟩,
    hwf, hlocal, ?_, ?_, hrc_len, hrc_mk, ?_, halice, hkyber, hpq, henc⟩
  · cases hri : s.state.remoteIdentity <;> simpa [hri] using hrem
  · revert hsender
    unfold Serialization.CanonSender
    cases G.sender <;> cases s.state.senderChain <;> intro hsender
    · exact True.intro
    · exact hsender
    · exact hsender
    · exact hsender.1
  · intro cg hcg
    obtain ⟨rc, hmem⟩ := mem_zip_of_mem_leftX hlen_eq hcg
    have hcc := hzip (cg, rc) hmem
    have hser_len : rc.senderRatchetKey.serialize.length = 33 :=
      PublicKey.serialize_length rc.senderRatchetKey
    exact ⟨hcc.1.trans (by rfl) ▸ hser_len, hcc.2⟩

theorem vecAt_prev_zero_eqX (out : BitVec 64) :
    vecAt A0 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    SeedLengthFacts.pure_true_sepConj hpure]

theorem deserOutRecordG_entails_binCanonSessionX {G0 : SessionGhost} (s : Session (List (BitVec 8)))
    (h0 : BinCanonSession G0 s) (hr : DeserializeScope ⟨some s⟩) (out : BitVec 64) :
    deserOutRecordG out ⟨some s⟩ ⊢
      ∃∗ G : SessionGhost, ⌜BinCanonSession G s⌝ ∗
        sessionRecordAt A0 out ⟨0#64, 8#64, some G⟩ ⟨some s⟩ := by
  have hAfter := ssgAfter_recFields ⟨some s⟩ hr s rfl
  have hRepr := prostSSG_repr ⟨some s⟩ hr s rfl (out + 0x18#64)
  have hdef :
      deserOutRecordG out ⟨some s⟩ =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          prostSSGAt A0 (out + 0x18#64) (ssgOf s) := by
    unfold deserOutRecordG
    rw [hAfter]
    ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right hRepr) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜Serialization.CanonSession G s⌝ ∗ sessionStateReprAt A0 (out + 0x18#64) G s)) =
      (⌜Serialization.CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          sessionStateReprAt A0 (out + 0x18#64) G s)) := by
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right G ?_
  refine Entails.pure_right (binCanonSession_of_canonSessionX h0 hcanon) ?_
  unfold sessionRecordAt
  dsimp only
  rw [vecAt_prev_zero_eqX]
  exact Entails.refl _

/-- Transport (generic in `prog`/`entry`): the exact deserialize contract implies
`(recordDeserializeOpenSpec A0).inImage img`. Copy of `sessionRecord_deserialize_base_generic`
with the unused environment premise dropped. -/
theorem recordDeserializeOpen_of_exactX {prog : Program} {entry : BitVec 64} (img : Obj.Image)
    (hdeser : subroutine_ok prog entry (deserializeExactSpecAtX img)) :
    subroutine_ok prog entry ((recordDeserializeOpenSpec A0).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨ptr, bs, out, sess⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre
  dsimp only [Spec.inImage, recordDeserializeOpenSpec] at hpre'
  rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hx8, hbs, hr, G0, hG0⟩, hmem⟩
  subst hbs
  have hlen_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length < 2 ^ 20 :=
    encodeRecord_length_lt hr
  have hx1 : s0.readReg64 .x1 =
      BitVec.ofNat 64 (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let x_deserialize : DeserializeGenGhost := ⟨ptr, out, ⟨some sess⟩⟩
  let R_deserialize : SepProp := (A0.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
      (recordDeserializeStack - recDeserializeStack) ∗ R)
  have hpre_deserialize :
      s0.mem ⊨ (deserializeExactSpecAtX img).pre x_deserialize s0 ∗ R_deserialize := by
    dsimp only [deserializeExactSpecAtX, deserializeGenSpecAt, x_deserialize, R_deserialize]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hr, hF, hsym⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine (hdeser.to_outcome x_deserialize R_deserialize s0 hpc hrun hpre_deserialize hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [deserializeExactSpecAtX, x_deserialize, R_deserialize] at hq
    have hrepr := deserOutRecordG_entails_binCanonSessionX sess hG0 hr out
    have hq' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr)))) hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    rcases hq' with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, recordDeserializeOpenSpec]
    rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [deserializeExactSpecAtX, deserializeGenSpecAt, allocPanic,
      Spec.inImage, recordDeserializeOpenSpec, R_deserialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ A0.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
          (recordDeserializeStack - recDeserializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (ProofLib.entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [deserializeExactSpecAtX, deserializeGenSpecAt] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · exact (not_satisfies_false_sepConj hq).elim

/-! ## Arbitrary-Allocator (`A : RustAlloc`) Representation & Transport -/

section ArbitraryAlloc
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.E2E.Record.DeserializeSeed
open CryptoGames.HMAC

/-- Exact-postcondition `SessionRecord::deserialize` contract for arbitrary `A : RustAlloc`
(`= deserializeExactSpecAtWA A img` by `rfl`). -/
noncomputable def deserializeExactSpecAtXA (A : RustAlloc) (img : Obj.Image) :
    Spec DeserializeGenGhost where
  pre := (deserializeGenSpecAtA A img).pre
  post := fun x s0 sf => deserOutRawGA A x s0 sf
  onPanic := (deserializeGenSpecAtA A img).onPanic

theorem vecAt_prev_zero_eqXA (A : RustAlloc) (out : BitVec 64) :
    vecAt A 24 8 (fun (_ : Unit) _ => emp) out 0#64 8#64 [] =
      (out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64) := by
  have hpure : (0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧
      (8#64 : BitVec 64) ≠ 0#64) := by decide
  unfold vecAt vecHeader vecBuf
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ite_true, sepConj_emp,
    SeedLengthFacts.pure_true_sepConj hpure]

private theorem deserialize_serialize_pk_ssgXA (pk : PublicKey) :
    PublicKey.deserialize pk.serialize = .ok pk := by
  unfold PublicKey.serialize PublicKey.deserialize
  rcases pk with ⟨⟨bs, hbs⟩⟩
  simp [hbs]; congr 1
  exact Subtype.ext (List.take_of_length_le (Nat.le_of_eq hbs))

private theorem serialize_pk_length_ssgXA (pk : PublicKey) :
    pk.serialize.length = 33 := by
  unfold PublicKey.serialize; simp [pk.bytes.toList_length]

private theorem serialize_ik_length_ssgXA (ik : IdentityKey) :
    ik.serialize.length = 33 :=
  serialize_pk_length_ssgXA ik.publicKey

private theorem arrayAt_map_entails_zipXA {α β γ : Type}
    (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (stride : Nat) :
    ∀ (xs : List α) (base : BitVec 64),
      (∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) →
      arrayAt elem1 stride base (xs.map f) ⊢
        ∃∗ gs : List γ,
          ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
            arrayAt elem2 stride base (gs.zip xs)
  | [], base, _ => by
    dsimp only [List.map, arrayAt]
    refine Entails.sepExists_right [] ?_
    exact Entails.pure_right ⟨rfl, fun _ h => by cases h⟩ (Entails.refl _)
  | x :: xs, base, h => by
    dsimp only [List.map, arrayAt]
    have hx := h x List.mem_cons_self base
    have hxs := arrayAt_map_entails_zipXA elem1 elem2 P f stride xs
      (base + BitVec.ofNat 64 stride) (fun y hy b => h y (List.mem_cons_of_mem x hy) b)
    refine Entails.trans (sepConj_mono hx hxs) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    apply Entails.sepExists_elim; intro g
    rw [sepConj_assoc]
    apply Entails.pure_left; intro hpx
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right (g :: gs) ?_
    have hlen' : (g :: gs).length = (x :: xs).length := by simp [hlen]
    have hpz' : ∀ gx ∈ (g :: gs).zip (x :: xs), P gx := by
      intro gx hgx; simp only [List.zip_cons_cons, List.mem_cons] at hgx
      rcases hgx with rfl | hgx
      · exact hpx
      · exact hpz gx hgx
    refine Entails.pure_right ⟨hlen', hpz'⟩ ?_
    dsimp only [List.zip_cons_cons, arrayAt]; exact Entails.refl _

private theorem vecAt_map_entails_zipXA {α β γ : Type} (A : RustAlloc)
    (stride align : Nat) (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (v cap ptr : BitVec 64) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) :
    vecAt A stride align elem1 v cap ptr (xs.map f) ⊢
      ∃∗ gs : List γ,
        ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
          vecAt A stride align elem2 v cap ptr (gs.zip xs) := by
  unfold vecAt vecBuf
  rw [List.length_map, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbuf
  by_cases hcap : cap = 0
  · subst hcap
    have hnil : xs = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hbuf.1)
    subst hnil
    refine Entails.sepExists_right [] ?_
    refine Entails.pure_right ⟨rfl, fun _ h => by cases h⟩ ?_
    rw [sepConj_pure_left_comm]; exact Entails.pure_right hbuf (Entails.refl _)
  · simp only [hcap, ↓reduceIte]
    have harr := arrayAt_map_entails_zipXA elem1 elem2 P f stride xs ptr h
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left harr))) ?_
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro gs
    rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_pure_left_comm]
    apply Entails.pure_left; rintro ⟨hlen, hpz⟩
    refine Entails.sepExists_right gs (Entails.pure_right ⟨hlen, hpz⟩ ?_)
    have hzip_len : (gs.zip xs).length = xs.length := by rw [List.length_zip, hlen, Nat.min_self]
    rw [hzip_len, sepConj_pure_left_comm]; exact Entails.pure_right hbuf (Entails.refl _)

private theorem vecOf_map_entails_vecAt_zipXA {α β γ : Type} (A : RustAlloc)
    (stride align : Nat) (elem1 : β → BitVec 64 → SepProp) (elem2 : γ × α → BitVec 64 → SepProp)
    (P : γ × α → Prop) (f : α → β) (v : BitVec 64) (xs : List α)
    (h : ∀ x ∈ xs, ∀ b : BitVec 64, elem1 (f x) b ⊢ ∃∗ g : γ, ⌜P (g, x)⌝ ∗ elem2 (g, x) b) :
    vecOf A stride align elem1 v (xs.map f) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ gs : List γ,
        ⌜gs.length = xs.length ∧ (∀ gx ∈ gs.zip xs, P gx)⌝ ∗
          vecAt A stride align elem2 v cap ptr (gs.zip xs) := by
  unfold vecOf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr
    (vecAt_map_entails_zipXA A stride align elem1 elem2 P f v cap ptr xs h))

private theorem prostMsgKeyAt_entails_messageKeyAtXA (A : RustAlloc) (mk : MessageKeyGenerator)
    (hseed : mk.seed.length = 32) (a : BitVec 64) :
    prostMsgKeyAt A mk a ⊢
      ∃∗ mg : MessageKeyGhost, ⌜True⌝ ∗ messageKeyAt A (mg, mk) a := by
  have hne : mk.seed ≠ [] := by intro h; rw [h] at hseed; cases hseed
  unfold prostMsgKeyAt vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro seedCap; apply Entails.sepExists_elim; intro seedPtr
  apply Entails.sepExists_elim; intro ivCap; apply Entails.sepExists_elim; intro ivPtr
  apply Entails.sepExists_elim; intro macCap; apply Entails.sepExists_elim; intro macPtr
  apply Entails.sepExists_elim; intro cipherCap; apply Entails.sepExists_elim; intro cipherPtr
  refine Entails.sepExists_right
    { cipher := ⟨cipherCap, cipherPtr⟩, mac := ⟨macCap, macPtr⟩,
      iv := ⟨ivCap, ivPtr⟩, seed := ⟨seedCap, seedPtr⟩ } ?_
  refine Entails.pure_right trivial ?_
  unfold messageKeyAt; exact Entails.pure_right hne (Entails.refl _)

private theorem prostChainKey_entails_optChainKeyAtXA (A : RustAlloc) (o : Option ChainKey) (a : BitVec 64) :
    (match o.map (fun ck => (ck.index, HMAC.keyToBytes32 ck.key)) with
     | none => ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24
     | some (i, k) => vecU8 A (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗
         memRegion (a + 0x64#64) 4) ⊢
      ∃∗ ckPin : VecPin, optChainKeyAt A ckPin o (a + 72#64) := by
  rcases o with _ | ck
  · dsimp only [Option.map, optChainKeyAt]
    refine Entails.sepExists_right ⟨0, 0⟩ ?_
    rw [show a + 72#64 + 8#64 = a + 0x50#64 by rw [BitVec.add_assoc]; rfl]; exact Entails.refl _
  · dsimp only [Option.map, optChainKeyAt]; unfold vecU8
    simp only [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right ⟨cap, ptr⟩ ?_
    rw [show a + 72#64 + 24#64 = a + 0x60#64 by rw [BitVec.add_assoc]; rfl,
      show a + 72#64 + 28#64 = a + 0x64#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _

private theorem prostChainGAt_recv_entails_chainAtXA (A : RustAlloc) (c : ReceiverChain)
    (hseeds : ∀ mk ∈ c.messageKeys, mk.seed.length = 32)
    (hmax : c.messageKeys.length ≤ maxMessageKeys) (a : BitVec 64) :
    prostChainGAt A a (recvChainG c) ⊢
      ∃∗ cg : ChainGhost, ⌜CanonChain (cg, c)⌝ ∗ chainAt A (cg, c) a := by
  unfold prostChainGAt recvChainG; dsimp only
  have hkeys :
      vecOf A 104 8 (fun mk b => prostMsgKeyAt A mk b) (a + 0x30#64) c.messageKeys ⊢
        ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64, ∃∗ keys : List MessageKeyGhost,
          ⌜keys.length = c.messageKeys.length ∧ (∀ gx ∈ keys.zip c.messageKeys, True)⌝ ∗
            vecAt A 104 8 (messageKeyAt A) (a + 0x30#64) mkCap mkPtr (keys.zip c.messageKeys) := by
    conv_lhs => rw [show c.messageKeys = c.messageKeys.map id by simp]
    exact vecOf_map_entails_vecAt_zipXA A 104 8 (fun mk b => prostMsgKeyAt A mk b)
      (messageKeyAt A) (fun _ => True) id (a + 0x30#64) c.messageKeys
      (fun mk hmk b => prostMsgKeyAt_entails_messageKeyAtXA A mk (hseeds mk hmk) b)
  have hck := prostChainKey_entails_optChainKeyAtXA A c.chainKey a
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono hkeys hck))) ?_
  unfold vecU8
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ckPin; apply Entails.sepExists_elim; intro mkCap
  apply Entails.sepExists_elim; intro mkPtr; apply Entails.sepExists_elim; intro keys
  apply Entails.sepExists_elim; intro privCap; apply Entails.sepExists_elim; intro privPtr
  apply Entails.sepExists_elim; intro srkCap; apply Entails.sepExists_elim; intro srkPtr
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hkeyslen, -⟩
  let cg : ChainGhost := {
    srk := ⟨srkCap, srkPtr, c.senderRatchetKey.serialize⟩, priv := ⟨privCap, privPtr, []⟩,
    mkCap := mkCap, mkPtr := mkPtr, keys := keys, ck := ckPin }
  refine Entails.sepExists_right cg (Entails.pure_right ⟨rfl, rfl⟩ ?_)
  unfold chainAt
  refine Entails.pure_right
    ⟨deserialize_serialize_pk_ssgXA c.senderRatchetKey, hmax, hkeyslen,
      serialize_pk_length_ssgXA c.senderRatchetKey, rfl⟩ ?_
  dsimp only [cg, vecGhostAt]; exact Entails.refl _

private theorem prostRecvG_entails_vecAt_chainAtXA (A : RustAlloc) (s : Session (List (BitVec 8)))
    (hseeds : SeedsLen32 s.state)
    (hmax : ∀ c ∈ s.state.receiverChains, c.messageKeys.length ≤ maxMessageKeys) (a : BitVec 64) :
    vecOf A 104 8 (fun c p => prostChainGAt A p c) a (s.state.receiverChains.map recvChainG) ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ chains : List ChainGhost,
        ⌜chains.length = s.state.receiverChains.length ∧
          (∀ gc ∈ chains.zip s.state.receiverChains, CanonChain gc)⌝ ∗
          vecAt A 104 8 (chainAt A) a cap ptr (chains.zip s.state.receiverChains) :=
  vecOf_map_entails_vecAt_zipXA A 104 8 (fun c p => prostChainGAt A p c)
    (chainAt A) CanonChain recvChainG a s.state.receiverChains
    (fun c hc b => prostChainGAt_recv_entails_chainAtXA A c (hseeds c hc) (hmax c hc) b)

private theorem vecAt_nil_prostMsgKeyAt_eq_messageKeyAtXA (A : RustAlloc) (v cap ptr : BitVec 64) :
    vecAt A 104 8 (fun mk b => prostMsgKeyAt A mk b) v cap ptr [] =
      vecAt A 104 8 (messageKeyAt A) v cap ptr [] := by
  unfold vecAt vecBuf arrayAt; rfl

private theorem prostSenderG_entails_optSenderChainAtXA (A : RustAlloc) (scOpt : Option SenderChain)
    (hclamp : ∀ sc, scOpt = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes)
    (ss : BitVec 64) :
    (match scOpt.map senderChainG with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ⊢
      ∃∗ sg : Option SenderChainGhost,
        ⌜CanonSender sg scOpt⌝ ∗ optSenderChainAt A (ss + 0x90#64) sg scOpt := by
  rcases scOpt with _ | sc
  · dsimp only [Option.map]; refine Entails.sepExists_right none (Entails.pure_right trivial ?_)
    unfold optSenderChainAt
    rw [show ss + 0x90#64 + 8#64 = ss + 0x98#64 by rw [BitVec.add_assoc]; rfl]; exact Entails.refl _
  · dsimp only [Option.map]; unfold prostChainGAt senderChainG vecU8 vecOf
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro ckCap; apply Entails.sepExists_elim; intro ckPtr
    apply Entails.sepExists_elim; intro mkCap; apply Entails.sepExists_elim; intro mkPtr
    apply Entails.sepExists_elim; intro privCap; apply Entails.sepExists_elim; intro privPtr
    apply Entails.sepExists_elim; intro srkCap; apply Entails.sepExists_elim; intro srkPtr
    let g : SenderChainGhost := {
      srk := ⟨srkCap, srkPtr, sc.ratchetKey.publicKey.serialize⟩,
      priv := ⟨privCap, privPtr, sc.ratchetKey.privateKey.bytes.toList⟩,
      mkCap := mkCap, mkPtr := mkPtr, ck := ⟨ckCap, ckPtr⟩ }
    refine Entails.sepExists_right (some g) (Entails.pure_right ⟨rfl, rfl⟩ ?_)
    unfold optSenderChainAt
    refine Entails.pure_right
      ⟨deserialize_serialize_pk_ssgXA _, rfl, hclamp sc rfl, serialize_pk_length_ssgXA _⟩ ?_
    dsimp only [g, vecGhostAt, optChainKeyAt]
    rw [vecAt_nil_prostMsgKeyAt_eq_messageKeyAtXA,
      show ss + 0x90#64 + 72#64 + 24#64 = ss + 0x90#64 + 0x60#64 by rw [BitVec.add_assoc]; rfl,
      show ss + 0x90#64 + 72#64 + 28#64 = ss + 0x90#64 + 0x64#64 by rw [BitVec.add_assoc]; rfl]
    exact Entails.refl _

private def pendingTail_ssgXA (w1 w2 : BitVec 32) : List (BitVec 8) :=
  unpack32 0#32 ++ (unpack32 w1 ++ (unpack64 0#64 ++ (unpack32 0#32 ++ unpack32 w2)))

private theorem pendingTail_pointsToBytes_ssgXA (ss : BitVec 64) (w1 w2 : BitVec 32) :
    ((ss + 0x110#64) ↦₃₂ 0#32) ∗ ((ss + 0x114#64) ↦₃₂ w1) ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
      ((ss + 0x120#64) ↦₃₂ 0#32) ∗ ((ss + 0x124#64) ↦₃₂ w2) =
      ((ss + 0xf8#64 + 24#64) ↦ₛ pendingTail_ssgXA w1 w2) := by
  have ha0 : ss + 0xf8#64 + 24#64 = ss + 0x110#64 := by rw [BitVec.add_assoc]; rfl
  have ha1 : ss + 0x110#64 + 4#64 = ss + 0x114#64 := by rw [BitVec.add_assoc]; rfl
  have ha2 : ss + 0x114#64 + 4#64 = ss + 0x118#64 := by rw [BitVec.add_assoc]; rfl
  have ha3 : ss + 0x118#64 + 8#64 = ss + 0x120#64 := by rw [BitVec.add_assoc]; rfl
  have ha4 : ss + 0x120#64 + 4#64 = ss + 0x124#64 := by rw [BitVec.add_assoc]; rfl
  unfold pendingTail_ssgXA
  rw [ha0, pointsToBytes_append, unpack32_length, ha1, pointsToBytes_append, unpack32_length,
    ha2, pointsToBytes_append, unpack64_length, ha3, pointsToBytes_append, unpack32_length, ha4]
  simp only [← pointsTo32_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]

private theorem prostPendingG_entails_optTailVecAtXA (A : RustAlloc) (s : Session (List (BitVec 8)))
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p →
      p.preKeyId = none ∧ p.signedPreKeyId = 0 ∧ p.timestamp = 0)
    (ss : BitVec 64) :
    (match s.pendingPreKey.map (fun p => p.baseKey.serialize) with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ⊢
      ∃∗ pg : Option TailVecGhost,
        ⌜CanonPending pg s.pendingPreKey ∧ PendingRel pg s.pendingPreKey ∧
          pg.isSome = s.state.pendingPreKey⌝ ∗
          optTailVecAt A 48 (ss + 0xf8#64) pg := by
  unfold Session.Wf at hwf
  rcases hpend : s.pendingPreKey with _ | p
  · dsimp only [Option.map]; refine Entails.sepExists_right none ?_
    refine Entails.pure_right ⟨trivial, trivial, by rw [hwf, hpend]; rfl⟩ ?_
    unfold optTailVecAt
    rw [show ss + 0xf8#64 + 8#64 = ss + 0x100#64 by rw [BitVec.add_assoc]; rfl]; exact Entails.refl _
  · dsimp only [Option.map]; obtain ⟨hpre, hspk, hts⟩ := hp p hpend
    unfold vecU8; rw [memRegion_four (ss + 0x114#64), memRegion_four (ss + 0x124#64)]
    simp only [sepExists_sepConj_right, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w2; apply Entails.sepExists_elim; intro w1
    apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
    let g : TailVecGhost := { vec := ⟨cap, ptr, p.baseKey.serialize⟩, tail := pendingTail_ssgXA w1 w2 }
    refine Entails.sepExists_right (some g) ?_
    have hrel : PendingRel (some g) (some p) := by
      refine ⟨deserialize_serialize_pk_ssgXA p.baseKey, ?_, ?_, ?_, serialize_pk_length_ssgXA p.baseKey⟩
      · rw [hpre]; rfl
      · rw [hts]; rfl
      · rw [hspk]; rfl
    refine Entails.pure_right ⟨rfl, hrel, by rw [hwf, hpend]; rfl⟩ ?_
    unfold optTailVecAt; refine Entails.pure_right (by rfl) ?_
    dsimp only [g, vecGhostAt]; rw [← pendingTail_pointsToBytes_ssgXA ss w1 w2]; exact Entails.refl _

/-- General-allocator decoded `SessionStructure` representation (`prostSSGAt A ⊢ sessionStateReprAt A`). -/
theorem prostSSG_reprA (A : RustAlloc) (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) (ss : BitVec 64) :
    prostSSGAt A ss (ssgOf s) ⊢
      ∃∗ G : SessionGhost, ⌜Serialization.CanonSession G s⌝ ∗ sessionStateReprAt A ss G s := by
  obtain ⟨⟨hr_in, hr_pq, hr_repr⟩, s', hs', hscope⟩ := hr
  cases hs.symm.trans hs'
  obtain ⟨-, hseeds, -, -⟩ := hr_in s hs
  have hpq : s.state.pqRatchetState = [] := hr_pq s hs
  obtain ⟨hmax_mk, hclamp, hwf, -⟩ := hr_repr s hs
  obtain ⟨-, hkyber, hlocReg, hremReg, halice, hpend_fields⟩ := hscope
  unfold prostSSGAt ssgOf; dsimp only
  have hrecv := prostRecvG_entails_vecAt_chainAtXA A s hseeds hmax_mk (ss + 0x48#64)
  have hsender := prostSenderG_entails_optSenderChainAtXA A s.state.senderChain hclamp ss
  have hpending := prostPendingG_entails_optTailVecAtXA A s hwf hpend_fields ss
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left hrecv)))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro chainsCap; apply Entails.sepExists_elim; intro chainsPtr
  apply Entails.sepExists_elim; intro chains
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hchains_len, hchains_canon⟩
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hsender))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro sg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; intro hsender_canon
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left hpending)))))))) ?_
  simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pg
  simp only [sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hpending_canon, hpending_rel, hpending_some⟩
  unfold vecU8; simp only [sepExists_sepConj_right, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro pqCap; apply Entails.sepExists_elim; intro pqPtr
  apply Entails.sepExists_elim; intro aliceCap; apply Entails.sepExists_elim; intro alicePtr
  apply Entails.sepExists_elim; intro rootCap; apply Entails.sepExists_elim; intro rootPtr
  apply Entails.sepExists_elim; intro rikCap; apply Entails.sepExists_elim; intro rikPtr
  apply Entails.sepExists_elim; intro likCap; apply Entails.sepExists_elim; intro likPtr
  let G : SessionGhost := {
    localIk := ⟨likCap, likPtr, s.state.localIdentity.serialize⟩,
    remoteIk := ⟨rikCap, rikPtr, (s.state.remoteIdentity.map IdentityKey.serialize).getD []⟩,
    root := ⟨rootCap, rootPtr⟩, chainsCap := chainsCap, chainsPtr := chainsPtr, chains := chains,
    alice := ⟨aliceCap, alicePtr, []⟩, pq := ⟨pqCap, pqPtr⟩,
    sender := sg, pending := pg, kyber := none, regIds := unpack64 0#64 }
  refine Entails.sepExists_right G
    (Entails.pure_right ⟨rfl, rfl, hsender_canon, hchains_len, hchains_canon, hpending_canon⟩ ?_)
  unfold sessionStateReprAt
  have hkyber_rel : KyberRel G.kyber s.pendingKyberPreKey := by rw [hkyber]; trivial
  have hreg1 : G.regIds.take 4 = leBytes 4 s.remoteRegistrationId.toNat := by
    dsimp only [G]; rw [hremReg]; rfl
  have hreg2 : (G.regIds.drop 4).take 4 = leBytes 4 s.localRegistrationId.toNat := by
    dsimp only [G]; rw [hlocReg]; rfl
  refine Entails.pure_right ⟨hpending_rel, hkyber_rel, halice.symm, hreg1, hreg2⟩ ?_
  unfold sessionStateAt
  have hrem_deser :
      match s.state.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey := by
    dsimp only [G]; rcases s.state.remoteIdentity with _ | ik
    · rfl
    · exact deserialize_serialize_pk_ssgXA ik.publicKey
  have hrem_len : s.state.remoteIdentity.isSome → G.remoteIk.bytes.length = 33 := by
    dsimp only [G]; rcases s.state.remoteIdentity with _ | ik <;> simp [serialize_ik_length_ssgXA]
  refine Entails.pure_right
    ⟨deserialize_serialize_pk_ssgXA s.state.localIdentity.publicKey,
      hrem_deser, hchains_len, hpending_some, rfl,
      serialize_ik_length_ssgXA s.state.localIdentity, hrem_len⟩ ?_
  dsimp only [G, vecGhostAt, optTailVecAt]
  rw [hpq, show ss + 0x128#64 + 8#64 = ss + 0x130#64 by rw [BitVec.add_assoc]; rfl,
    ← pointsTo64_eq_pointsToBytes]
  simp only [sepConj_assoc]; exact Entails.refl _

/-- General-allocator `deserOutRecordGA` representation (`deserOutRecordGA A ⊢ sessionRecordAt A`),
matching the `hRepr` premise of `deserializeBodyGWA_ok`. -/
theorem deserReprGA_ok (A : RustAlloc) (r : SessionRecord (List (BitVec 8))) (hr : DeserializeScope r)
    (out : BitVec 64) :
    deserOutRecordGA A out r ⊢
      ∃∗ g : RecordGhost, ⌜Serialization.CanonRecord g r⌝ ∗ sessionRecordAt A out g r := by
  obtain ⟨s, hs, _⟩ := hr.2
  have hAfter := ssgAfter_recFields r hr s hs
  have hRepr := prostSSG_reprA A r hr s hs (out + 0x18#64)
  have hdef :
      deserOutRecordGA A out r =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          prostSSGAt A (out + 0x18#64) (ssgOf s) := by
    unfold deserOutRecordGA; rw [hAfter]; ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right hRepr) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜Serialization.CanonSession G s⌝ ∗ sessionStateReprAt A (out + 0x18#64) G s)) =
      (⌜Serialization.CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          sessionStateReprAt A (out + 0x18#64) G s)) := by ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right ⟨0#64, 8#64, some G⟩ ?_
  refine Entails.pure_right (by unfold Serialization.CanonRecord Serialization.CanonCur; rw [hs]; exact hcanon) ?_
  unfold sessionRecordAt; rw [hs]; dsimp only
  rw [vecAt_prev_zero_eqXA A]; exact Entails.refl _

theorem deserOutRecordGA_entails_binCanonSessionX (A : RustAlloc) {G0 : SessionGhost}
    (s : Session (List (BitVec 8))) (h0 : BinCanonSession G0 s)
    (hr : DeserializeScope ⟨some s⟩) (out : BitVec 64) :
    deserOutRecordGA A out ⟨some s⟩ ⊢
      ∃∗ G : SessionGhost, ⌜BinCanonSession G s⌝ ∗
        sessionRecordAt A out ⟨0#64, 8#64, some G⟩ ⟨some s⟩ := by
  have hAfter := ssgAfter_recFields ⟨some s⟩ hr s rfl
  have hRepr := prostSSG_reprA A ⟨some s⟩ hr s rfl (out + 0x18#64)
  have hdef :
      deserOutRecordGA A out ⟨some s⟩ =
        ((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          prostSSGAt A (out + 0x18#64) (ssgOf s) := by
    unfold deserOutRecordGA; rw [hAfter]; ac_rfl
  rw [hdef]
  refine Entails.trans (sepConj_mono_right hRepr) ?_
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun G => ?_
  have h1 :
      (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
        (⌜Serialization.CanonSession G s⌝ ∗ sessionStateReprAt A (out + 0x18#64) G s)) =
      (⌜Serialization.CanonSession G s⌝ ∗
        (((out ↦₆₄ 0#64) ∗ ((out + 8#64) ↦₆₄ 8#64) ∗ ((out + 0x10#64) ↦₆₄ 0#64)) ∗
          sessionStateReprAt A (out + 0x18#64) G s)) := by ac_rfl
  rw [h1]
  refine Entails.pure_left fun hcanon => ?_
  refine Entails.sepExists_right G ?_
  refine Entails.pure_right (binCanonSession_of_canonSessionX h0 hcanon) ?_
  unfold sessionRecordAt; dsimp only
  rw [vecAt_prev_zero_eqXA A]; exact Entails.refl _

/-- Transport (generic in `prog`/`entry`/`A`): the exact deserialize contract implies
`(recordDeserializeOpenSpec A).inImage img`. -/
theorem recordDeserializeOpen_of_exactXA {prog : Program} {entry : BitVec 64}
    (A : RustAlloc) (img : Obj.Image)
    (hdeser : subroutine_ok prog entry (deserializeExactSpecAtXA A img)) :
    subroutine_ok prog entry ((recordDeserializeOpenSpec A).inImage img) := by
  refine subroutine_ok_outcome_intro fun ⟨ptr, bs, out, sess⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' := hpre
  dsimp only [Spec.inImage, recordDeserializeOpenSpec] at hpre'
  rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hF, hsym⟩, hpre'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hx8, hbs, hr, G0, hG0⟩, hmem⟩
  subst hbs
  have hlen_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length < 2 ^ 20 :=
    encodeRecord_length_lt hr
  have hx1 : s0.readReg64 .x1 =
      BitVec.ofNat 64 (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let x_deserialize : DeserializeGenGhost := ⟨ptr, out, ⟨some sess⟩⟩
  let R_deserialize : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
      (recordDeserializeStack - recDeserializeStack) ∗ R
  have hpre_deserialize :
      s0.mem ⊨ (deserializeExactSpecAtXA A img).pre x_deserialize s0 ∗ R_deserialize := by
    dsimp only [deserializeExactSpecAtXA, deserializeGenSpecAtA, x_deserialize, R_deserialize]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hr, hF, hsym⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine (hdeser.to_outcome x_deserialize R_deserialize s0 hpc hrun hpre_deserialize hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [deserializeExactSpecAtXA, deserOutRawGA, x_deserialize, R_deserialize] at hq
    have hrepr := deserOutRecordGA_entails_binCanonSessionX A sess hG0 hr out
    have hq' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr)))) hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    rcases hq' with ⟨htr, hq_mem⟩
    dsimp only [Spec.inImage, recordDeserializeOpenSpec]
    rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [deserializeExactSpecAtXA, deserializeGenSpecAtA, allocPanic,
      Spec.inImage, recordDeserializeOpenSpec, R_deserialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗
        memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
          (recordDeserializeStack - recDeserializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (ProofLib.entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [deserializeExactSpecAtXA, deserializeGenSpecAtA] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · exact (not_satisfies_false_sepConj hq).elim

end ArbitraryAlloc

/-! ## Relocatable `[LibsignalPlacement]` Exact-to-Open Transport -/

section Placed

theorem L1_DeserTransportX_Placed : True := trivial

/-- Image-free exact-postcondition `SessionRecord::deserialize` contract (`deserOutRecordG` niche form),
definitionally equal to `deserializeExactRawSpecW`. -/
noncomputable def deserializeExactRawSpecX : Spec DeserializeGenGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.p ∧
      s.readReg64 .x1 = BitVec.ofNat 64 (CryptoVerification.E2E.Record.encodeRecord x.r).length ∧
      s.readReg64 .x8 = x.out ∧ DeserializeScope x.r⌝ ∗
      (x.p ↦ₛ CryptoVerification.E2E.Record.encodeRecord x.r) ∗
      memRegion x.out 368 ∗ stackAt s.sp recDeserializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (x.p ↦ₛ CryptoVerification.E2E.Record.encodeRecord x.r) ∗
      deserOutRecordG x.out x.r ∗
      stackAt s0.sp recDeserializeStack
  onPanic := allocPanic

/-- Relocatable exact-postcondition `SessionRecord::deserialize` contract carrying
`LibsignalCodeRoLoaded lsmpl`. -/
noncomputable abbrev deserializeExactPlacedSpecX [LibsignalPlacement] : Spec DeserializeGenGhost :=
  LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl deserializeExactRawSpecX

/-- Relocatable transport (generic in `prog`, `entry`, and `pl`): the exact deserialize contract
under `LibsignalCodeRoLoaded pl` implies `withLsCodeRoLoaded pl (recordDeserializeOpenSpec A0)`. -/
theorem recordDeserializeOpen_placed_of_exactX {prog : Program} {entry : BitVec 64}
    (pl : Obj.MultiPlacement)
    (hdeser : subroutine_ok prog entry
      (LibsignalTripleRatchet.withLsCodeRoLoaded pl deserializeExactRawSpecX)) :
    subroutine_ok prog entry
      (LibsignalTripleRatchet.withLsCodeRoLoaded pl (recordDeserializeOpenSpec A0)) := by
  refine subroutine_ok_outcome_intro fun ⟨ptr, bs, out, sess⟩ R s0 hpc hrun hpre hal => ?_
  obtain ⟨hcrl, hpre'⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [recordDeserializeOpenSpec] at hpre'
  rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj] at hpre'
  rcases hpre' with ⟨⟨hx0, hx1_nat, hx8, hbs, hr, G0, hG0⟩, hmem⟩
  subst hbs
  have hlen_lt : (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length < 2 ^ 20 :=
    encodeRecord_length_lt hr
  have hx1 : s0.readReg64 .x1 =
      BitVec.ofNat 64 (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let x_deserialize : DeserializeGenGhost := ⟨ptr, out, ⟨some sess⟩⟩
  let R_deserialize : SepProp := (A0.pool ∗
    memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
      (recordDeserializeStack - recDeserializeStack) ∗ R)
  have hpre_deserialize :
      s0.mem ⊨ (LibsignalTripleRatchet.withLsCodeRoLoaded pl deserializeExactRawSpecX).pre
        x_deserialize s0 ∗ R_deserialize := by
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeExactRawSpecX,
      x_deserialize, R_deserialize]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcrl, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx8, hr⟩, ?_⟩
    convert hmem using 1; ac_rfl
  refine (hdeser.to_outcome x_deserialize R_deserialize s0 hpc hrun hpre_deserialize hal).mono_outcome ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeExactRawSpecX,
      x_deserialize, R_deserialize] at hq
    have hrepr := deserOutRecordG_entails_binCanonSessionX sess hG0 hr out
    have hq' := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hrepr)))) hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq'
    rcases hq' with ⟨htr, hq_mem⟩
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, recordDeserializeOpenSpec]
    rw [stackAt_recordDeserialize_splitX s0.sp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨htr, ?_⟩
    convert hq_mem using 1; ac_rfl
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeExactRawSpecX,
      allocPanic, recordDeserializeOpenSpec, R_deserialize] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
    rcases hq with ⟨hfail, hq_mem⟩
    refine ⟨hfail, ?_⟩
    have hany : (anyHeap ∗ A0.pool ∗
        memRegion (s0.sp - BitVec.ofNat 64 recordDeserializeStack)
          (recordDeserializeStack - recDeserializeStack)) ∗ R ⊢ anyHeap ∗ R :=
      sepConj_mono_left (ProofLib.entails_anyHeap _)
    refine Satisfies.mono hany ?_
    convert hq_mem using 1; ac_rfl
  · dsimp only [LibsignalTripleRatchet.withLsCodeRoLoaded, deserializeExactRawSpecX,
      deserializeGenSpec] at hq
    rw [satisfies_pure_sepConj] at hq
    exact hq.1.elim
  · exact (not_satisfies_false_sepConj hq).elim

end Placed

end Proofs.libsignal.Hooks2
