/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bundle
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs

/-!
# Equivalence of `parseBundleDir` and `readBundleV`

Establishes the two-way equivalence between the byte-level parser `parseBundleDir` and `readBundleV`
on 1813-byte `PreKeyBundleFields` encodings, along with pointwise `filesOf` evaluation on
`PublicBundle.files`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Parity

open Arm64 Arm64.Process CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunRefine CryptoVerification.SignalSession.Cli.RunProofs

private theorem ite_pos {α : Type} {c : Prop} [inst : Decidable c] (hc : c) {a b : α} :
    (if c then a else b) = a := match inst with | isTrue _ => rfl | isFalse h => absurd hc h
private theorem ite_neg {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c) {a b : α} :
    (if c then a else b) = b := match inst with | isTrue h => absurd h hc | isFalse _ => rfl
private theorem dite_pos {α : Type} {c : Prop} [inst : Decidable c] (hc : c)
    {a : c → α} {b : ¬ c → α} : (if h : c then a h else b h) = a hc :=
  match inst with | isTrue _ => rfl | isFalse h => absurd hc h
private theorem dite_neg {α : Type} {c : Prop} [inst : Decidable c] (hc : ¬ c)
    {a : c → α} {b : ¬ c → α} : (if h : c then a h else b h) = b hc :=
  match inst with | isTrue h => absurd h hc | isFalse _ => rfl

/-! ## `parseBundleDir` and `readBundleV` Equivalence -/

/-- Normalizes a serialized Curve25519 public key (`0x05 :: rest` with `32 ≤ rest.length`). -/
def normDjbKey : List (BitVec 8) → Option (List (BitVec 8))
  | b :: rest => if b = 5#8 ∧ 32 ≤ rest.length then some (5#8 :: rest.take 32) else none
  | [] => none

/-- Normalizes a serialized Kyber-1024 public key (`0x08 :: rest` with `rest.length = 1568`). -/
def normKyberKey : List (BitVec 8) → Option (List (BitVec 8))
  | b :: rest => if b = 8#8 ∧ rest.length = 1568 then some (8#8 :: rest) else none
  | [] => none

/-- Byte-level bundle directory parser matching `read_bundle` at `device = 1#8`. -/
def parseBundleDir (d : String → Option (List (BitVec 8))) (dirName : String) : Option PublicBundle :=
  let fileBytes (name : String) : List (BitVec 8) := (d (dirName ++ "/" ++ name)).getD []
  do
    let identityKey ← normDjbKey (fileBytes "identity-key")
    let registrationId ← RunCompose.readU32LE (fileBytes "registration-id")
    let (signedId, spkKeyRaw, signedSig) ← splitSigned (fileBytes "signed-pre-key")
    let signedKey ← normDjbKey spkKeyRaw
    let (kyberId, kpkKeyRaw, kyberSig) ← splitSigned (fileBytes "kyber-pre-key")
    let kyberKey ← normKyberKey kpkKeyRaw
    let oneTime ← (if (fileBytes "one-time-pre-key").isEmpty then some none else do
        let (opkId, opkKeyRaw) ← splitId (fileBytes "one-time-pre-key")
        let opkKey ← normDjbKey opkKeyRaw
        some (some (opkId, opkKey)))
    some { identityKey, registrationId, signedId, signedKey, signedSig,
           kyberId, kyberKey, kyberSig, oneTime }

/-- 1813-byte serialized bundle representation of a `PublicBundle` (`PreKeyBundleFields.bytes` layout). -/
def publicBundleBytes (pb : PublicBundle) : List (BitVec 8) :=
  let opk : List (BitVec 8) := match pb.oneTime with
    | some (i, k) => 1#8 :: CryptoVerification.SignalSession.le32 i ++ k
    | none => 0#8 :: List.replicate 37 0#8
  CryptoVerification.SignalSession.le32 pb.registrationId ++ opk ++
    CryptoVerification.SignalSession.le32 pb.signedId ++ pb.signedKey ++ pb.signedSig ++
    CryptoVerification.SignalSession.le32 pb.kyberId ++ pb.kyberKey ++ pb.kyberSig ++ pb.identityKey

theorem le32_eq_toLEBytes4 (v : BitVec 32) :
    CryptoVerification.SignalSession.le32 v = CryptoVerification.LibsignalAesCbc.toLEBytes 4 v := rfl

theorem publicBundleBytes_publicBundleOf (b : PreKeyBundleFields) :
    publicBundleBytes (publicBundleOf b) = b.bytes := by
  unfold publicBundleBytes publicBundleOf PreKeyBundleFields.bytes djbKey kyberKey
  cases b.opk with
  | none => simp only [Option.map_none, le32_eq_toLEBytes4]
  | some p => rcases p with ⟨_, _⟩; simp only [Option.map_some, le32_eq_toLEBytes4]

theorem publicBundleBytes_publicBundleOf_length (b : PreKeyBundleFields) :
    (publicBundleBytes (publicBundleOf b)).length = 1813 := by
  unfold publicBundleBytes publicBundleOf
    CryptoVerification.SignalSession.le32 djbKey kyberKey
  cases b.opk with | none => simp | some p => rcases p with ⟨_, _⟩; simp

theorem bundleEOf?_bundleVE (b : PreKeyBundleFields) :
    RunProofs.bundleEOf? (RunRefine.bundleVE b) = some b := by
  rcases b with ⟨regId, opk, spkId, spkPub, spkSig, kpkId, kpkPub, kpkSig, idPub⟩
  simp only [RunProofs.bundleEOf?, RunRefine.bundleVE, spkSig.toList_length, kpkSig.toList_length,
    kpkPub.toList_length, ↓reduceDIte]
  congr 1; cases opk with | none => rfl | some p => rcases p with ⟨_, _⟩; rfl

theorem bundleVE_injective : Function.Injective RunRefine.bundleVE := fun b1 b2 h => by
  have h1 := bundleEOf?_bundleVE b1; rw [h, bundleEOf?_bundleVE b2] at h1
  exact Option.some.inj h1.symm

theorem publicBundleOf_injective : Function.Injective publicBundleOf := by
  intro b1 b2 h
  rcases b1 with ⟨reg1, opk1, spkId1, spkPub1, spkSig1, kpkId1, kpkPub1, kpkSig1, idPub1⟩
  rcases b2 with ⟨reg2, opk2, spkId2, spkPub2, spkSig2, kpkId2, kpkPub2, kpkSig2, idPub2⟩
  simp only [publicBundleOf, PublicBundle.mk.injEq, djbKey, kyberKey, List.cons.injEq, true_and] at h
  obtain ⟨hid, rfl, rfl, hspkPub, hspkSig, rfl, hkpkPub, hkpkSig, hopk⟩ := h
  cases Subtype.ext hid; cases Subtype.ext hspkPub; cases Subtype.ext hspkSig
  cases Subtype.ext hkpkPub; cases Subtype.ext hkpkSig; congr 1
  rcases opk1 with _ | ⟨i1, k1⟩ <;> rcases opk2 with _ | ⟨i2, k2⟩
  · rfl
  · cases hopk
  · cases hopk
  · injection hopk with hp; injection hp with hi hk; injection hk with _ hk'
    exact congrArg some (Prod.ext hi (Subtype.ext hk'))

private theorem pubDeserialize_iff_normDjbKey (bs : List (BitVec 8)) :
    (∀ pk : PublicKey, exceptOpt (PublicKey.deserialize bs) = some pk →
      normDjbKey bs = some (djbKey pk.bytes)) ∧
    (∀ kbs : List (BitVec 8), normDjbKey bs = some kbs →
      ∃ v : List.Vector (BitVec 8) 32,
        kbs = djbKey v ∧ exceptOpt (PublicKey.deserialize bs) = some ⟨v⟩) := by
  have h5 : ¬ (5#8 ≠ djbType) := not_not.mpr rfl
  constructor
  · intro pk h; cases bs with
    | nil => cases h
    | cons b rest =>
      dsimp only [PublicKey.deserialize] at h
      by_cases hb : b = 5#8
      · subst hb; rw [ite_neg h5] at h
        by_cases hge : 32 ≤ rest.length
        · rw [dite_pos hge] at h; injection h with h; subst h
          dsimp only [normDjbKey, djbKey]; exact ite_pos ⟨rfl, hge⟩
        · rw [dite_neg hge] at h; cases h
      · have hb' : b ≠ djbType := hb; rw [ite_pos hb'] at h; cases h
  · intro kbs h; cases bs with
    | nil => cases h
    | cons b rest =>
      dsimp only [normDjbKey] at h
      by_cases hcond : b = 5#8 ∧ 32 ≤ rest.length
      · rw [ite_pos hcond] at h; obtain ⟨rfl, hge⟩ := hcond; injection h with hkbs; subst hkbs
        refine ⟨⟨rest.take 32, by simp [hge]⟩, rfl, ?_⟩
        dsimp only [PublicKey.deserialize]; rw [ite_neg h5, dite_pos hge]; rfl
      · rw [ite_neg hcond] at h; cases h

private theorem decodeIdentityKey_iff_normDjbKey (bs : List (BitVec 8)) :
    (∀ ik : IdentityKey, exceptOpt (decodeIdentityKey bs) = some ik →
      normDjbKey bs = some (djbKey ik.publicKey.bytes)) ∧
    (∀ kbs : List (BitVec 8), normDjbKey bs = some kbs →
      ∃ v : List.Vector (BitVec 8) 32,
        kbs = djbKey v ∧ exceptOpt (decodeIdentityKey bs) = some ⟨⟨v⟩⟩) := by
  constructor
  · intro ik h; unfold decodeIdentityKey at h
    cases hp : PublicKey.deserialize bs with
    | error _ => rw [hp] at h; cases h
    | ok pk =>
      rw [hp] at h; injection h with h; subst h
      exact (pubDeserialize_iff_normDjbKey bs).1 pk (by rw [hp]; rfl)
  · intro kbs h; obtain ⟨v, rfl, hp⟩ := (pubDeserialize_iff_normDjbKey bs).2 kbs h
    refine ⟨v, rfl, ?_⟩; unfold decodeIdentityKey
    cases hdes : PublicKey.deserialize bs with
    | error _ => rw [hdes] at hp; cases hp
    | ok pk => rw [hdes] at hp; injection hp with hp; subst hp; rfl

private theorem kemPkDeserialize_iff_normKyberKey (bs : List (BitVec 8)) :
    (∀ kpk : List (BitVec 8),
      (match RunProofs.kemPkDeserialize bs with | .ok key => some key | _ => none) = some kpk →
      ∃ v : List.Vector (BitVec 8) 1568, kpk = v.toList ∧ normKyberKey bs = some (kyberKey v)) ∧
    (∀ kbs : List (BitVec 8), normKyberKey bs = some kbs →
      ∃ v : List.Vector (BitVec 8) 1568, kbs = kyberKey v ∧
        (match RunProofs.kemPkDeserialize bs with | .ok key => some key | _ => none) =
          some v.toList) := by
  constructor
  · intro kpk h; cases bs with
    | nil => cases h
    | cons b rest =>
      dsimp only [RunProofs.kemPkDeserialize, RunProofs.kemPkLen] at h
      by_cases hb : b = 8#8
      · subst hb; rw [ite_neg (not_not.mpr rfl)] at h
        by_cases hlen : rest.length = 1568
        · rw [ite_neg (not_not.mpr hlen)] at h; injection h with hkpk; subst hkpk
          refine ⟨⟨rest, hlen⟩, rfl, ?_⟩; dsimp only [normKyberKey, kyberKey]; exact ite_pos ⟨rfl, hlen⟩
        · rw [ite_pos hlen] at h; cases h
      · rw [ite_pos hb] at h; cases h
  · intro kbs h; cases bs with
    | nil => cases h
    | cons b rest =>
      dsimp only [normKyberKey] at h
      by_cases hcond : b = 8#8 ∧ rest.length = 1568
      · rw [ite_pos hcond] at h; obtain ⟨rfl, hlen⟩ := hcond; injection h with hkbs; subst hkbs
        refine ⟨⟨rest, hlen⟩, rfl, ?_⟩; dsimp only [RunProofs.kemPkDeserialize, RunProofs.kemPkLen]
        rw [ite_neg (not_not.mpr rfl), ite_neg (not_not.mpr hlen)]; rfl
      · rw [ite_neg hcond] at h; cases h

private theorem splitSigned_sig_len {bs : List (BitVec 8)} {id : BitVec 32}
    {key sig : List (BitVec 8)} (h : splitSigned bs = some (id, key, sig)) : sig.length = 64 := by
  unfold splitSigned at h
  cases hs : splitId bs with
  | none => rw [hs] at h; cases h
  | some p =>
    rcases p with ⟨_, rest⟩; rw [hs] at h
    change (if 64 ≤ rest.length then some _ else none) = some _ at h
    by_cases hge : 64 ≤ rest.length
    · rw [ite_pos hge] at h; injection h with hEq
      rcases Prod.mk.inj (Prod.mk.inj hEq).2 with ⟨_, rfl⟩; simp only [List.length_drop]; omega
    · rw [ite_neg hge] at h; cases h

private def opkReadV (bs : List (BitVec 8)) : Option (Option (BitVec 32 × PublicKey)) :=
  if bs.isEmpty then some none else match splitId bs with
    | none => none
    | some (opkId, opkKey) => match exceptOpt (PublicKey.deserialize opkKey) with
      | none => none | some k => some (some (opkId, k))

private def opkParseB (bs : List (BitVec 8)) : Option (Option (BitVec 32 × List (BitVec 8))) :=
  if bs.isEmpty then some none else match splitId bs with
    | none => none
    | some (opkId, opkKeyRaw) => match normDjbKey opkKeyRaw with
      | none => none | some opkKey => some (some (opkId, opkKey))

private theorem opkReadV_iff_opkParseB (bs : List (BitVec 8)) :
    (∀ opk, opkReadV bs = some opk →
      opkParseB bs = some (opk.map fun (i, k) => (i, djbKey k.bytes))) ∧
    (∀ oneTime, opkParseB bs = some oneTime →
      ∃ opkE : Option (BitVec 32 × List.Vector (BitVec 8) 32),
        oneTime = (opkE.map fun (i, k) => (i, djbKey k)) ∧
        opkReadV bs = some (opkE.map fun (i, k) => (i, (⟨k⟩ : PublicKey)))) := by
  unfold opkReadV opkParseB; by_cases hemp : bs.isEmpty = true
  · rw [ite_pos hemp, ite_pos hemp]
    exact ⟨fun opk h => by injection h with h; subst h; rfl,
           fun oneTime h => by injection h with h; exact ⟨none, h.symm, rfl⟩⟩
  · rw [ite_neg hemp, ite_neg hemp]; constructor
    · intro opk h; cases hsp : splitId bs with
      | none => rw [hsp] at h; cases h
      | some p =>
        rcases p with ⟨opkId, raw⟩; rw [hsp] at h; dsimp only at h ⊢
        cases hokD : exceptOpt (PublicKey.deserialize raw) with
        | none => rw [hokD] at h; cases h
        | some pk =>
          rw [hokD] at h; injection h with h; subst h
          rw [(pubDeserialize_iff_normDjbKey raw).1 pk hokD]; rfl
    · intro oneTime h; cases hsp : splitId bs with
      | none => rw [hsp] at h; cases h
      | some p =>
        rcases p with ⟨opkId, raw⟩; rw [hsp] at h; dsimp only at h ⊢
        cases hokN : normDjbKey raw with
        | none => rw [hokN] at h; cases h
        | some kbs =>
          rw [hokN] at h; injection h with h; subst h
          obtain ⟨v, rfl, hokD⟩ := (pubDeserialize_iff_normDjbKey raw).2 kbs hokN
          exact ⟨some (opkId, v), rfl, by rw [hokD]; rfl⟩

private def readBundleBytes (ikB regB spkB kpkB opkB : List (BitVec 8)) : Option BundleV :=
  match exceptOpt (decodeIdentityKey ikB) with
  | none => none
  | some idKey =>
    match RunCompose.readU32LE regB with
    | none => none
    | some regId =>
      match splitSigned spkB with
      | none => none
      | some (spkId, spkKey, spkSig) =>
        match splitSigned kpkB with
        | none => none
        | some (kpkId, kpkKey, kpkSig) =>
          match opkReadV opkB with
          | none => none
          | some opk =>
            match exceptOpt (PublicKey.deserialize spkKey) with
            | none => none
            | some spk =>
              match (match RunProofs.kemPkDeserialize kpkKey with | .ok key => some key | _ => none) with
              | none => none
              | some kpk =>
                some { idKey, regId, device := 1#8, spkId, spk, spkSig, kpkId, kpk, kpkSig, opk }

private def parseBundleBytes (ikB regB spkB kpkB opkB : List (BitVec 8)) : Option PublicBundle :=
  match normDjbKey ikB with
  | none => none
  | some identityKey =>
    match RunCompose.readU32LE regB with
    | none => none
    | some registrationId =>
      match splitSigned spkB with
      | none => none
      | some (signedId, spkKeyRaw, signedSig) =>
        match normDjbKey spkKeyRaw with
        | none => none
        | some signedKey =>
          match splitSigned kpkB with
          | none => none
          | some (kyberId, kpkKeyRaw, kyberSig) =>
            match normKyberKey kpkKeyRaw with
            | none => none
            | some kyberKey =>
              match opkParseB opkB with
              | none => none
              | some oneTime =>
                some { identityKey, registrationId, signedId, signedKey, signedSig,
                       kyberId, kyberKey, kyberSig, oneTime }

private theorem parseBundleDir_eq_parseBundleBytes
    (d : String → Option (List (BitVec 8))) (dirName : String) :
    parseBundleDir d dirName = parseBundleBytes
      ((d (dirName ++ "/" ++ "identity-key")).getD [])
      ((d (dirName ++ "/" ++ "registration-id")).getD [])
      ((d (dirName ++ "/" ++ "signed-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "kyber-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []) := by
  unfold parseBundleDir parseBundleBytes opkParseB; dsimp only [bind, Option.bind]
  cases normDjbKey ((d (dirName ++ "/" ++ "identity-key")).getD []) with
  | none => rfl
  | some _ =>
    dsimp only [Option.bind]
    cases RunCompose.readU32LE ((d (dirName ++ "/" ++ "registration-id")).getD []) with
    | none => rfl
    | some _ =>
      dsimp only [Option.bind]
      cases splitSigned ((d (dirName ++ "/" ++ "signed-pre-key")).getD []) with
      | none => rfl
      | some p1 =>
        rcases p1 with ⟨_, spkKeyRaw, _⟩; dsimp only [Option.bind]
        cases normDjbKey spkKeyRaw with
        | none => rfl
        | some _ =>
          dsimp only [Option.bind]
          cases splitSigned ((d (dirName ++ "/" ++ "kyber-pre-key")).getD []) with
          | none => rfl
          | some p2 =>
            rcases p2 with ⟨_, kpkKeyRaw, _⟩; dsimp only [Option.bind]
            cases normKyberKey kpkKeyRaw with
            | none => rfl
            | some _ =>
              dsimp only [Option.bind]
              by_cases hemp : ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []).isEmpty = true
              · rw [ite_pos hemp, ite_pos hemp]
              · rw [ite_neg hemp, ite_neg hemp]
                cases splitId ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []) with
                | none => rfl
                | some p3 =>
                  rcases p3 with ⟨_, opkKeyRaw⟩; dsimp only [Option.bind]
                  cases normDjbKey opkKeyRaw <;> rfl

private theorem readBundleV_eq_readBundleBytes
    {F : FsFiles} {d : String → Option (List (BitVec 8))} {dirName : String}
    (hF : ∀ name ∈ RunCompose.bundleNames, RunCompose.bundleFile F (bytesOfString dirName) name =
      some ((d (dirName ++ "/" ++ name)).getD [])) :
    RunCompose.readBundleV F (bytesOfString dirName) 1#8 = readBundleBytes
      ((d (dirName ++ "/" ++ "identity-key")).getD [])
      ((d (dirName ++ "/" ++ "registration-id")).getD [])
      ((d (dirName ++ "/" ++ "signed-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "kyber-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []) := by
  unfold RunCompose.readBundleV readBundleBytes opkReadV
  rw [hF "identity-key" (by decide), hF "registration-id" (by decide),
      hF "signed-pre-key" (by decide), hF "kyber-pre-key" (by decide),
      hF "one-time-pre-key" (by decide)]
  dsimp only [bind, Option.bind]
  cases exceptOpt (decodeIdentityKey ((d (dirName ++ "/" ++ "identity-key")).getD [])) with
  | none => rfl
  | some _ =>
    dsimp only [Option.bind]
    cases RunCompose.readU32LE ((d (dirName ++ "/" ++ "registration-id")).getD []) with
    | none => rfl
    | some _ =>
      dsimp only [Option.bind]
      cases splitSigned ((d (dirName ++ "/" ++ "signed-pre-key")).getD []) with
      | none => rfl
      | some p1 =>
        rcases p1 with ⟨_, spkKey, _⟩; dsimp only [Option.bind]
        cases splitSigned ((d (dirName ++ "/" ++ "kyber-pre-key")).getD []) with
        | none => rfl
        | some p2 =>
          rcases p2 with ⟨_, kpkKey, _⟩; dsimp only [Option.bind]
          by_cases hemp : ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []).isEmpty = true
          · rw [ite_pos hemp, ite_pos hemp]; dsimp only [Option.bind]
            cases exceptOpt (PublicKey.deserialize spkKey) with
            | none => rfl
            | some _ =>
              dsimp only [Option.bind]
              cases RunProofs.kemPkDeserialize kpkKey <;> rfl
          · rw [ite_neg hemp, ite_neg hemp]
            cases splitId ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []) with
            | none => rfl
            | some p3 =>
              rcases p3 with ⟨_, opkKey⟩; dsimp only [Option.bind]
              cases exceptOpt (PublicKey.deserialize opkKey) with
              | none => rfl
              | some _ =>
                dsimp only [Option.bind]
                cases exceptOpt (PublicKey.deserialize spkKey) with
                | none => rfl
                | some _ =>
                  dsimp only [Option.bind]
                  cases RunProofs.kemPkDeserialize kpkKey <;> rfl

private theorem bundleBytes_dichotomy (ikB regB spkB kpkB opkB : List (BitVec 8)) :
    (readBundleBytes ikB regB spkB kpkB opkB = none ∧
      parseBundleBytes ikB regB spkB kpkB opkB = none) ∨
    ∃ b_e : PreKeyBundleFields, readBundleBytes ikB regB spkB kpkB opkB = some (RunRefine.bundleVE b_e) ∧
      parseBundleBytes ikB regB spkB kpkB opkB = some (publicBundleOf b_e) := by
  unfold readBundleBytes parseBundleBytes
  cases hik : normDjbKey ikB with
  | none =>
    have hikD : exceptOpt (decodeIdentityKey ikB) = none := by
      cases hd : exceptOpt (decodeIdentityKey ikB) with
      | none => rfl
      | some ik => rw [(decodeIdentityKey_iff_normDjbKey ikB).1 ik hd] at hik; cases hik
    rw [hikD]; exact .inl ⟨rfl, rfl⟩
  | some identityKey =>
    obtain ⟨vId, rfl, hikD⟩ := (decodeIdentityKey_iff_normDjbKey ikB).2 identityKey hik
    rw [hikD]; dsimp only
    cases RunCompose.readU32LE regB with
    | none => exact .inl ⟨rfl, rfl⟩
    | some regId =>
      dsimp only; cases hspkS : splitSigned spkB with
      | none => exact .inl ⟨rfl, rfl⟩
      | some spkT =>
        rcases spkT with ⟨spkId, spkKeyRaw, spkSig⟩; dsimp only
        cases hspkN : normDjbKey spkKeyRaw with
        | none =>
          have hspkD : exceptOpt (PublicKey.deserialize spkKeyRaw) = none := by
            cases hd : exceptOpt (PublicKey.deserialize spkKeyRaw) with
            | none => rfl
            | some pk => rw [(pubDeserialize_iff_normDjbKey spkKeyRaw).1 pk hd] at hspkN; cases hspkN
          refine .inl ⟨?_, rfl⟩; cases splitSigned kpkB with
          | none => rfl
          | some kpkT =>
            rcases kpkT with ⟨_, _, _⟩; dsimp only
            cases opkReadV opkB with | none => rfl | some _ => dsimp only; rw [hspkD]
        | some spkKeyBs =>
          obtain ⟨vSpk, rfl, hspkD⟩ := (pubDeserialize_iff_normDjbKey spkKeyRaw).2 spkKeyBs hspkN
          dsimp only; cases hkpkS : splitSigned kpkB with
          | none => exact .inl ⟨rfl, rfl⟩
          | some kpkT =>
            rcases kpkT with ⟨kpkId, kpkKeyRaw, kpkSig⟩; dsimp only
            cases hkpkN : normKyberKey kpkKeyRaw with
            | none =>
              have hkpkD : (match RunProofs.kemPkDeserialize kpkKeyRaw with
                  | .ok key => some key | _ => none) = none := by
                cases hd : (match RunProofs.kemPkDeserialize kpkKeyRaw with
                    | .ok key => some key | _ => none) with
                | none => rfl
                | some kpk =>
                  obtain ⟨_, _, hn⟩ := (kemPkDeserialize_iff_normKyberKey kpkKeyRaw).1 kpk hd
                  rw [hn] at hkpkN; cases hkpkN
              refine .inl ⟨?_, rfl⟩; cases opkReadV opkB with
              | none => rfl
              | some _ => dsimp only; rw [hspkD]; dsimp only; rw [hkpkD]
            | some kpkKeyBs =>
              obtain ⟨vKpk, rfl, hkpkD⟩ :=
                (kemPkDeserialize_iff_normKyberKey kpkKeyRaw).2 kpkKeyBs hkpkN
              dsimp only; cases hopkP : opkParseB opkB with
              | none =>
                have hopkV : opkReadV opkB = none := by
                  cases hd : opkReadV opkB with
                  | none => rfl
                  | some opk => rw [(opkReadV_iff_opkParseB opkB).1 opk hd] at hopkP; cases hopkP
                rw [hopkV]; exact .inl ⟨rfl, rfl⟩
              | some oneTime =>
                obtain ⟨opkE, rfl, hopkD⟩ := (opkReadV_iff_opkParseB opkB).2 oneTime hopkP
                let b_e : PreKeyBundleFields :=
                  { regId := regId, opk := opkE, spkId := spkId, spkPub := vSpk,
                    spkSig := ⟨spkSig, splitSigned_sig_len hspkS⟩, kpkId := kpkId, kpkPub := vKpk,
                    kpkSig := ⟨kpkSig, splitSigned_sig_len hkpkS⟩, idPub := vId }
                refine .inr ⟨b_e, ?_, rfl⟩
                rw [hopkD]; dsimp only; rw [hspkD]; dsimp only; rw [hkpkD]; rfl

theorem parseBundleDir_of_readBundleV_eq_some
    {F : FsFiles} {d : String → Option (List (BitVec 8))} {dirName : String} {bv : BundleV}
    (hF : ∀ name ∈ RunCompose.bundleNames, RunCompose.bundleFile F (bytesOfString dirName) name =
      some ((d (dirName ++ "/" ++ name)).getD []))
    (hr : RunCompose.readBundleV F (bytesOfString dirName) 1#8 = some bv) :
    ∃! b_e : PreKeyBundleFields, bv = RunRefine.bundleVE b_e ∧ RunProofs.bundleEOf? bv = some b_e ∧
      parseBundleDir d dirName = some (publicBundleOf b_e) := by
  rw [readBundleV_eq_readBundleBytes hF] at hr
  rcases bundleBytes_dichotomy
      ((d (dirName ++ "/" ++ "identity-key")).getD [])
      ((d (dirName ++ "/" ++ "registration-id")).getD [])
      ((d (dirName ++ "/" ++ "signed-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "kyber-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []) with ⟨hn, _⟩ | ⟨b_e, hrv, hpb⟩
  · rw [hn] at hr; cases hr
  · have hbv : bv = RunRefine.bundleVE b_e := Option.some.inj (hr.symm.trans hrv)
    rw [parseBundleDir_eq_parseBundleBytes]
    exact ⟨b_e, ⟨hbv, hbv ▸ bundleEOf?_bundleVE b_e, hpb⟩,
      fun _ ⟨hb', _, _⟩ => bundleVE_injective (hb'.symm.trans hbv)⟩

theorem readBundleV_eq_some_of_parseBundleDir
    {F : FsFiles} {d : String → Option (List (BitVec 8))} {dirName : String} {pb : PublicBundle}
    (hF : ∀ name ∈ RunCompose.bundleNames, RunCompose.bundleFile F (bytesOfString dirName) name =
      some ((d (dirName ++ "/" ++ name)).getD []))
    (hp : parseBundleDir d dirName = some pb) :
    ∃! b_e : PreKeyBundleFields, publicBundleOf b_e = pb ∧
      RunCompose.readBundleV F (bytesOfString dirName) 1#8 = some (RunRefine.bundleVE b_e) ∧
      publicBundleBytes pb = b_e.bytes ∧
      (publicBundleBytes pb).length = 1813 := by
  rw [parseBundleDir_eq_parseBundleBytes] at hp; rw [readBundleV_eq_readBundleBytes hF]
  rcases bundleBytes_dichotomy
      ((d (dirName ++ "/" ++ "identity-key")).getD [])
      ((d (dirName ++ "/" ++ "registration-id")).getD [])
      ((d (dirName ++ "/" ++ "signed-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "kyber-pre-key")).getD [])
      ((d (dirName ++ "/" ++ "one-time-pre-key")).getD []) with ⟨_, hn⟩ | ⟨b_e, hrv, hpb⟩
  · rw [hn] at hp; cases hp
  · have hpbEq : publicBundleOf b_e = pb := Option.some.inj (hpb.symm.trans hp)
    exact ⟨b_e, ⟨hpbEq, hrv, hpbEq ▸ publicBundleBytes_publicBundleOf b_e,
      hpbEq ▸ publicBundleBytes_publicBundleOf_length b_e⟩,
      fun _ ⟨hb', _, _, _⟩ => publicBundleOf_injective (hb'.trans hpbEq.symm)⟩

theorem readBundleV_eq_some_iff_bundleE
    {F : FsFiles} {d : String → Option (List (BitVec 8))} {dirName : String}
    (hF : ∀ name ∈ RunCompose.bundleNames, RunCompose.bundleFile F (bytesOfString dirName) name =
      some ((d (dirName ++ "/" ++ name)).getD [])) :
    (∀ bv, RunCompose.readBundleV F (bytesOfString dirName) 1#8 = some bv →
      ∃! b_e : PreKeyBundleFields, bv = RunRefine.bundleVE b_e ∧ RunProofs.bundleEOf? bv = some b_e ∧
        parseBundleDir d dirName = some (publicBundleOf b_e)) ∧
    (∀ pb, parseBundleDir d dirName = some pb →
      ∃ b_e : PreKeyBundleFields, publicBundleOf b_e = pb ∧
        RunCompose.readBundleV F (bytesOfString dirName) 1#8 = some (RunRefine.bundleVE b_e) ∧
        publicBundleBytes pb = b_e.bytes ∧
        (publicBundleBytes pb).length = 1813) :=
  ⟨fun _ hr => parseBundleDir_of_readBundleV_eq_some hF hr,
   fun _ hp => let ⟨b_e, hb, _⟩ := readBundleV_eq_some_of_parseBundleDir hF hp; ⟨b_e, hb⟩⟩

theorem readBundleV_eq_none_iff
    {F : FsFiles} {d : String → Option (List (BitVec 8))} {dirName : String}
    (hF : ∀ name ∈ RunCompose.bundleNames, RunCompose.bundleFile F (bytesOfString dirName) name =
      some ((d (dirName ++ "/" ++ name)).getD [])) :
    RunCompose.readBundleV F (bytesOfString dirName) 1#8 = none ↔ parseBundleDir d dirName = none := by
  constructor
  · intro hr; cases hp : parseBundleDir d dirName with
    | none => rfl
    | some _ =>
      obtain ⟨_, ⟨_, hr', _, _⟩, _⟩ := readBundleV_eq_some_of_parseBundleDir hF hp
      rw [hr] at hr'; cases hr'
  · intro hp; cases hr : RunCompose.readBundleV F (bytesOfString dirName) 1#8 with
    | none => rfl
    | some _ =>
      obtain ⟨_, ⟨_, _, hp'⟩, _⟩ := parseBundleDir_of_readBundleV_eq_some hF hr
      rw [hp] at hp'; cases hp'

/-! ## Pointwise `filesOf` on `PublicBundle.files` -/

private def FlatBundleEntry (p : String) : Prop :=
  (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast = [[bundleDir]] ∧
  normalizePath p ≠ [bundleDir]

private instance (p : String) : Decidable (FlatBundleEntry p) := by
  unfold FlatBundleEntry; infer_instance

private def bundleLookup (q : FsPath) : List (String × List (BitVec 8)) → Option (List (BitVec 8)) :=
  List.foldl (fun v f => if q = normalizePath f.1 then some f.2 else v) none

private theorem filesFold_flatBundle :
    ∀ (l : List (String × List (BitVec 8))) (a : FsState),
      (∀ f ∈ l, FlatBundleEntry f.1) →
      fileOfEntry (a.entries [bundleDir]) = none →
      ∀ q, fileOfEntry ((filesFold l a).entries q) =
        (bundleLookup q l).or (fileOfEntry (a.entries q))
  | [], a, _, _, q => by simp [filesFold, bundleLookup]
  | (p, bs) :: rest, a, hl, ha, q => by
    obtain ⟨hdrop, hne⟩ := hl (p, bs) (List.mem_cons_self ..)
    let a1 := (((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) a).setFile p (some (.file bs))
    have ha1_eq : a1 = (a.setEntry [bundleDir] (some .dir)).setEntry
        (normalizePath p) (some (.file bs)) := by
      simp [a1, hdrop, FsState.setFile]
    have hnep : [bundleDir] ≠ normalizePath p := fun h => hne h.symm
    have ha1_dir : fileOfEntry (a1.entries [bundleDir]) = none := by
      rw [ha1_eq]
      simp [FsState.setEntry, hnep, fileOfEntry]
    have ha1_q : ∀ r, fileOfEntry (a1.entries r) =
        if r = normalizePath p then some bs else fileOfEntry (a.entries r) := by
      intro r
      rw [ha1_eq]
      by_cases hrp : r = normalizePath p
      · simp [FsState.setEntry, hrp, fileOfEntry]
      · have hrhs : (if r = normalizePath p then some bs else fileOfEntry (a.entries r)) =
            fileOfEntry (a.entries r) := by simp [hrp]
        rw [hrhs]
        by_cases hrb : r = [bundleDir]
        · subst hrb
          rw [ha]
          simp [FsState.setEntry, hnep, fileOfEntry]
        · simp [FsState.setEntry, hrp, hrb]
    have ih := filesFold_flatBundle rest a1
      (fun f hf => hl f (List.mem_cons_of_mem _ hf)) ha1_dir q
    have hfold_or : ∀ (xs : List (String × List (BitVec 8))) (v1 v2 : Option (List (BitVec 8))),
        xs.foldl (fun v f => if q = normalizePath f.1 then some f.2 else v) (v1.or v2) =
          (xs.foldl (fun v f => if q = normalizePath f.1 then some f.2 else v) v1).or v2 := by
      intro xs
      induction xs with
      | nil => intro v1 v2; rfl
      | cons x xs ihx =>
        intro v1 v2
        simp only [List.foldl_cons]
        split
        · rw [← ihx (some x.2) v2]; rfl
        · exact ihx v1 v2
    simp only [filesFold, List.foldl_cons]
    change fileOfEntry ((filesFold rest a1).entries q) = _
    rw [ih, ha1_q q]
    unfold bundleLookup
    simp only [List.foldl_cons]
    rw [← hfold_or rest (if q = normalizePath p then some bs else none) (fileOfEntry (a.entries q))]
    conv_rhs =>
      rw [show ((if q = normalizePath p then some bs else none).or (fileOfEntry (a.entries q))) =
            (none : Option (List (BitVec 8))).or
              ((if q = normalizePath p then some bs else none).or (fileOfEntry (a.entries q))) from rfl]
    rw [hfold_or rest none]
    congr 1
    split <;> rfl

private theorem filesOf_flatBundle {l : List (String × List (BitVec 8))}
    (hl : ∀ f ∈ l, FlatBundleEntry f.1) {p : String}
    (hstdio : normalizePath p ∉ stdioPaths.map normalizePath)
    (hne : (normalizePath p).isEmpty = false) :
    filesOf l p = bundleLookup (normalizePath p) l := by
  unfold filesOf fsView
  simp only [hstdio, ↓reduceIte]
  show fileOfEntry ((Arm64.Process.initFsState { files := l }).files p) = _
  simp only [FsState.files, FsState.getEntry, hne, Bool.false_eq_true, ↓reduceIte]
  rw [initFsState_entries { files := l } (normalizePath p) hstdio]
  have hdir : dirsFold [] ({} : FsState) = {} := rfl
  rw [hdir, filesFold_flatBundle l {} hl (NoFiles.base [bundleDir]) (normalizePath p),
    NoFiles.base (normalizePath p), Option.or_none]

private theorem publicBundle_files_flatEntry (b : PublicBundle) :
    ∀ f ∈ b.files bundleDir, FlatBundleEntry f.1 := by
  intro f hf
  simp only [PublicBundle.files, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with (rfl | rfl | rfl | rfl) | hot
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · cases ho : b.oneTime with
    | none => simp [ho] at hot
    | some ik =>
      simp only [ho, List.mem_singleton] at hot
      subst hot; dsimp only; decide

/-- Pointwise evaluation of `filesOf (b.files bundleDir)` at each of the five bundle file names. -/
theorem filesOf_publicBundle_files (b : PublicBundle) :
    filesOf (b.files bundleDir) (bundleDir ++ "/" ++ "identity-key") = some b.identityKey ∧
    filesOf (b.files bundleDir) (bundleDir ++ "/" ++ "registration-id") =
      some (CryptoVerification.SignalSession.le32 b.registrationId) ∧
    filesOf (b.files bundleDir) (bundleDir ++ "/" ++ "signed-pre-key") =
      some (CryptoVerification.SignalSession.le32 b.signedId ++ b.signedKey ++ b.signedSig) ∧
    filesOf (b.files bundleDir) (bundleDir ++ "/" ++ "kyber-pre-key") =
      some (CryptoVerification.SignalSession.le32 b.kyberId ++ b.kyberKey ++ b.kyberSig) ∧
    filesOf (b.files bundleDir) (bundleDir ++ "/" ++ "one-time-pre-key") =
      (b.oneTime.map fun (id, key) => CryptoVerification.SignalSession.le32 id ++ key) := by
  have hfl := publicBundle_files_flatEntry b
  have p_ik : normalizePath (bundleDir ++ "/" ++ "identity-key") = ["bundle", "identity-key"] := rfl
  have p_ik' : normalizePath (bundleDir ++ "/identity-key") = ["bundle", "identity-key"] := rfl
  have p_reg : normalizePath (bundleDir ++ "/" ++ "registration-id") = ["bundle", "registration-id"] := rfl
  have p_reg' : normalizePath (bundleDir ++ "/registration-id") = ["bundle", "registration-id"] := rfl
  have p_spk : normalizePath (bundleDir ++ "/" ++ "signed-pre-key") = ["bundle", "signed-pre-key"] := rfl
  have p_spk' : normalizePath (bundleDir ++ "/signed-pre-key") = ["bundle", "signed-pre-key"] := rfl
  have p_kpk : normalizePath (bundleDir ++ "/" ++ "kyber-pre-key") = ["bundle", "kyber-pre-key"] := rfl
  have p_kpk' : normalizePath (bundleDir ++ "/kyber-pre-key") = ["bundle", "kyber-pre-key"] := rfl
  have p_opk : normalizePath (bundleDir ++ "/" ++ "one-time-pre-key") = ["bundle", "one-time-pre-key"] := rfl
  have p_opk' : normalizePath (bundleDir ++ "/one-time-pre-key") = ["bundle", "one-time-pre-key"] := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [filesOf_flatBundle hfl (by decide) (by decide)]
    cases ho : b.oneTime with
    | none => simp [PublicBundle.files, ho, bundleLookup, p_ik, p_ik', p_reg', p_spk', p_kpk']
    | some p =>
      obtain ⟨id, key⟩ := p
      simp [PublicBundle.files, ho, bundleLookup, p_ik, p_ik', p_reg', p_spk', p_kpk', p_opk']
  · rw [filesOf_flatBundle hfl (by decide) (by decide)]
    cases ho : b.oneTime with
    | none => simp [PublicBundle.files, ho, bundleLookup, p_reg, p_reg', p_spk', p_kpk']
    | some p =>
      obtain ⟨id, key⟩ := p
      simp [PublicBundle.files, ho, bundleLookup, p_reg, p_reg', p_spk', p_kpk', p_opk']
  · rw [filesOf_flatBundle hfl (by decide) (by decide)]
    cases ho : b.oneTime with
    | none => simp [PublicBundle.files, ho, bundleLookup, p_spk, p_spk', p_kpk']
    | some p =>
      obtain ⟨id, key⟩ := p
      simp [PublicBundle.files, ho, bundleLookup, p_spk, p_spk', p_kpk', p_opk']
  · rw [filesOf_flatBundle hfl (by decide) (by decide)]
    cases ho : b.oneTime with
    | none => simp [PublicBundle.files, ho, bundleLookup, p_kpk, p_kpk']
    | some p =>
      obtain ⟨id, key⟩ := p
      simp [PublicBundle.files, ho, bundleLookup, p_kpk, p_kpk', p_opk']
  · rw [filesOf_flatBundle hfl (by decide) (by decide)]
    cases ho : b.oneTime with
    | none => simp [PublicBundle.files, ho, bundleLookup, p_opk, p_ik', p_reg', p_spk', p_kpk']
    | some p =>
      obtain ⟨id, key⟩ := p
      simp [PublicBundle.files, ho, bundleLookup, p_opk, p_opk']

end LibsignalBinary.Proofs.SignalSession.Cli.Parity
