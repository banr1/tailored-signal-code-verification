/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Spec
import all Init.Data.String.Defs
import all Init.Data.String.Basic
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.List.SplitOn.Basic
import LibsignalBinary.Proofs.RecordCodecs.RoundTrip

/-!
# Path, Account, and Key-Derivation Lemmas for `initOk₀_pqInit`

Proves peer address length and `cliIo.pathOk` guards (`nameLt`, `textLt`, `sessPathOk`, `idPathOk`,
`sessPathLt`, `idPathLt`), distinct `ServiceId` parsing on `Party.A` vs `Party.B` (`distinctAcct`),
and X25519 scalar clamping idempotence with `IdentityKeyPair.tryFrom` decoding (`idPairDerived`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.RunProofs.InitS0

open Arm64 Arm64.Process
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.RecordCodecs
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunRefine

/-! ## Pure `String` / `utf8` reduction helpers -/

private theorem drop_getElem_cons {α : Type} :
    ∀ (xs : List α) (i : Nat) (h : i < xs.length), xs[i]'h :: xs.drop (i + 1) = xs.drop i
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, h => drop_getElem_cons xs i (Nat.lt_of_succ_lt_succ h)

private theorem drop_of_le {α : Type} :
    ∀ (xs : List α) (i : Nat), xs.length ≤ i → xs.drop i = []
  | [], _, _ => by simp
  | _ :: _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: xs, i + 1, h => drop_of_le xs i (Nat.le_of_succ_le_succ h)

private theorem byteArray_loop_eq (arr : Array UInt8) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop ⟨arr⟩ i r = r.reverse ++ arr.toList.drop i := by
  unfold ByteArray.toList.loop
  split
  · next h =>
    have hi : i < arr.size := h
    have his : i < arr.toList.length := by simpa using hi
    have hget : (ByteArray.mk arr).get! i = arr.toList[i]'his := by
      simp [ByteArray.get!, getElem!_pos arr i hi]
    rw [byteArray_loop_eq arr (i + 1) ((ByteArray.mk arr).get! i :: r), hget,
      List.reverse_cons, List.append_assoc, List.singleton_append, drop_getElem_cons arr.toList i his]
  · next h =>
    have hi : arr.toList.length ≤ i := by
      have : ¬ i < arr.size := h
      simp at *; omega
    rw [drop_of_le arr.toList i hi, List.append_nil]
termination_by arr.size - i
decreasing_by
  have : i < arr.size := ‹_›
  omega

private theorem toList_toByteArray_eq (l : List UInt8) : l.toByteArray.toList = l := by
  unfold ByteArray.toList
  have h1 : l.toByteArray = ⟨l.toArray⟩ := by
    ext1
    exact List.data_toByteArray
  rw [h1, byteArray_loop_eq]
  simp

private theorem ofList_toList_eq (s : String) : String.ofList s.toList = s := by
  simp

theorem string_ne_of_toList {s1 s2 : String} (h : s1.toList ≠ s2.toList) : s1 ≠ s2 :=
  fun e => h (congrArg String.toList e)

theorem utf8_eq_flatMap (s : String) :
    utf8 s = (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  conv_lhs => rw [← ofList_toList_eq s]
  unfold utf8
  simp only [String.toUTF8, String.toByteArray_ofList, List.utf8Encode, toList_toByteArray_eq]

private theorem tri_utf8_eq_flatMap (s : String) :
    LibsignalTripleRatchetRepr.utf8 s =
      (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat := by
  conv_lhs => rw [← ofList_toList_eq s]
  unfold LibsignalTripleRatchetRepr.utf8
  simp only [String.toUTF8, String.toByteArray_ofList, List.utf8Encode, toList_toByteArray_eq]

private theorem pniPrefix_eq : pniPrefix = [0x50#8, 0x4e#8, 0x49#8, 0x3a#8] := by
  unfold pniPrefix
  rw [tri_utf8_eq_flatMap]
  rfl

/-! ## Peer address lengths and `cliIo.pathOk` guards -/

private theorem not_stdio_of_not_lt {c : List Char} (h : '<' ∉ c) :
    stdioPaths.contains (String.ofList c) = false := by
  cases hc : stdioPaths.contains (String.ofList c) with
  | false => rfl
  | true =>
    have hs := List.contains_iff_mem.mp hc
    have hlt : '<' ∈ (String.ofList c).toList := by
      unfold stdioPaths at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with hs | hs | hs <;> rw [hs] <;> decide
    rw [String.toList_ofList] at hlt
    exact absurd hlt h

private theorem pathOk_of_split2 {p : List (BitVec 8)} {c1 c2 : List Char}
    (hascii : ∀ b ∈ p, b.toNat < 128)
    (hlen : p.length < cliPathMaxBytes)
    (hsplit : (p.map fun b => Char.ofNat b.toNat).splitOn '/' = [c1, c2])
    (h1 : (!isUnmodelledPathComponent c1 && !c1.contains '\x00') = true) (hlt1 : '<' ∉ c1)
    (h2 : (!isUnmodelledPathComponent c2 && !c2.contains '\x00') = true) (hlt2 : '<' ∉ c2)
    (hc1 : decide (c1.length ≤ NAME_MAX) = true)
    (hc2 : decide (c2.length ≤ NAME_MAX) = true) :
    cliIo.pathOk p := by
  refine ⟨?_, ⟨hascii, ?_⟩, hlen⟩
  · unfold PathOk pathComps pathStr
    rw [String.toList_ofList, hsplit, List.all_cons, List.all_cons, List.all_nil,
      h1, h2, not_stdio_of_not_lt hlt1, not_stdio_of_not_lt hlt2]
    rfl
  · unfold pathComps pathStr
    rw [String.toList_ofList, hsplit, List.all_cons, List.all_cons, List.all_nil, hc1, hc2]
    rfl

theorem nameLt_party (P : Party) : (addrValE P).name.length < 2 ^ 32 := by
  cases P <;> simp only [addrValE, utf8_eq_flatMap, partyAddressName] <;> decide

theorem textLt_party (P : Party) : (addressText (addrValE P)).length < 2 ^ 32 := by
  cases P <;> simp only [addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName] <;> decide

theorem sessPathLt_party (P : Party) :
    (pathOf (utf8 "sessions") (addressText (addrValE P))).length < 2 ^ 32 := by
  cases P <;>
    simp only [pathOf, addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName] <;>
    decide

theorem idPathLt_party (P : Party) :
    (pathOf (utf8 "identities") (addrValE P).name).length < 2 ^ 32 := by
  cases P <;> simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName] <;> decide

theorem sessPathOk_party (P : Party) :
    cliIo.pathOk (pathOf (utf8 "sessions") (addressText (addrValE P))) := by
  cases P
  · refine pathOk_of_split2
      (c1 := "sessions".toList) (c2 := "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1".toList) ?_ ?_ ?_
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [pathOf, addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName]; decide
  · refine pathOk_of_split2
      (c1 := "sessions".toList) (c2 := "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1".toList) ?_ ?_ ?_
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [pathOf, addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, addressText, decimalText, utf8_eq_flatMap, partyAddressName]; decide

theorem idPathOk_party (P : Party) :
    cliIo.pathOk (pathOf (utf8 "identities") (addrValE P).name) := by
  cases P
  · refine pathOk_of_split2
      (c1 := "identities".toList) (c2 := "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b".toList) ?_ ?_ ?_
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName]; decide
  · refine pathOk_of_split2
      (c1 := "identities".toList) (c2 := "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6".toList) ?_ ?_ ?_
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName]; decide
    · simp only [pathOf, addrValE, utf8_eq_flatMap, partyAddressName]; decide

/-! ## Distinct `ServiceId`s -/

private theorem serviceIdParse_A_head :
    (serviceIdParse uuidTryParse (addrValE .A).name).map (fun s => s.2.toList.head?) =
      some (some 0x8a#8) := by
  unfold addrValE serviceIdParse
  rw [pniPrefix_eq, utf8_eq_flatMap]
  rfl

private theorem serviceIdParse_B_head :
    (serviceIdParse uuidTryParse (addrValE .B).name).map (fun s => s.2.toList.head?) =
      some (some 0x5d#8) := by
  unfold addrValE serviceIdParse
  rw [pniPrefix_eq, utf8_eq_flatMap]
  rfl

theorem distinctAcct_party (P : Party) :
    ¬ ∃ sid, serviceIdParse uuidTryParse (addrValE P.other).name = some sid ∧
      serviceIdParse uuidTryParse (addrValE P).name = some sid := by
  rintro ⟨sid, h1, h2⟩
  cases P
  · have hA := serviceIdParse_A_head
    have hB := serviceIdParse_B_head
    rw [Party.other] at h1
    rw [h1] at hB
    rw [h2] at hA
    exact absurd (hA.symm.trans hB) (by decide)
  · have hA := serviceIdParse_A_head
    have hB := serviceIdParse_B_head
    rw [Party.other] at h1
    rw [h1] at hA
    rw [h2] at hB
    exact absurd (hA.symm.trans hB) (by decide)

/-! ## Scalar clamping idempotence and `IdentityKeyPair.tryFrom` -/

private theorem clamp_lo_idem (b : BitVec 8) : (b &&& 0xf8#8) &&& 0xf8#8 = b &&& 0xf8#8 := by
  rw [BitVec.and_assoc]
  rfl

private theorem clamp_hi_idem (b : BitVec 8) :
    (((b &&& 0x7f#8) ||| 0x40#8) &&& 0x7f#8) ||| 0x40#8 = (b &&& 0x7f#8) ||| 0x40#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases b.getLsbD i <;> cases (0x7f#8).getLsbD i <;> cases (0x40#8).getLsbD i <;> rfl

theorem clampScalar_idem (sk : List.Vector (BitVec 8) 32) :
    Ratchet.clampScalar (Ratchet.clampScalar sk) = Ratchet.clampScalar sk := by
  rcases sk with ⟨l, hl⟩
  match l, hl with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
     b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], _ =>
    dsimp [Ratchet.clampScalar, List.Vector.get, List.Vector.set]
    rw [clamp_lo_idem, clamp_hi_idem]

/-- The encoded bytes of `st`'s `identity-key-pair` entry in `encodeDir W st`. -/
def ikBytes (W : PEParams) (st : PqParty) : List (BitVec 8) :=
  IdentityKeyPairStructure.encode
    ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩

theorem tryFrom_ikBytes (W : PEParams) (st : PqParty) :
    IdentityKeyPair.tryFrom (ikBytes W st) =
      .ok ⟨⟨(keyPairOf W.C st.me.idPriv).publicKey⟩, ⟨Ratchet.clampScalar st.me.idPriv⟩⟩ := by
  have hdec := IdentityKeyPairStructure.decode_encode
    ⟨djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩
    (by simp [djbKey]) (by simp)
  have hpub : decodeIdentityKey (djbKey (keyPairOf W.C st.me.idPriv).publicKey.bytes) =
      .ok ⟨(keyPairOf W.C st.me.idPriv).publicKey⟩ :=
    decodeIdentityKey_serialize ⟨(keyPairOf W.C st.me.idPriv).publicKey⟩
  have hpriv : deserializePrivateKey st.me.idPriv.toList = .ok ⟨Ratchet.clampScalar st.me.idPriv⟩ := by
    rcases st.me.idPriv with ⟨l, hl⟩
    simp [deserializePrivateKey, hl]
  simp only [ikBytes, IdentityKeyPair.tryFrom, hdec]
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [hpub]
  dsimp only
  rw [hpriv]

end CryptoVerification.SignalSession.Cli.RunProofs.InitS0
