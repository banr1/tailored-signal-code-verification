/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import all Init.Data.Repr
import all Init.Data.String.Defs

/-!
# PQXDH Step Scrubbing and Model-Preservation Helpers

Proves `scrub` lookup identities on `pqInputs` (`IsScrubbedPath`) and preservation of `PqPartyInv`
across `pqInitModel`, `pqSendModel`, `pqRecvWhisperModel`, and `pqRecvPrekeyModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.CREF.Cli

open DY DY.Comparse
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.SignalSession
open Symbolic.Swarm.TRREF.SpqrSemOf (bytesToVec)

/-! ## `IsScrubbedPath` and `scrub` identities -/

/-- Paths removed by `scrub`: `coins` and anything under `bundle/`. -/
def IsScrubbedPath (p : String) : Bool :=
  SamePath p coinsFile || (Arm64.normalizePath p).head? == some bundleDir

theorem isScrubbedPath_congr {p q : String}
    (h : Arm64.normalizePath p = Arm64.normalizePath q) :
    IsScrubbedPath p = IsScrubbedPath q := by
  simp [IsScrubbedPath, SamePath, h]

private theorem not_scrubbed_of_head {p h : String}
    (hh : (Arm64.normalizePath p).head? = some h) (hc : h ≠ "coins") (hb : h ≠ "bundle") :
    IsScrubbedPath p = false := by
  have h1 : SamePath p coinsFile = false := beq_false_of_ne fun heq => hc <| Option.some.inj <| by
    have hcf : (Arm64.normalizePath coinsFile).head? = some "coins" := by decide
    rw [heq, hcf] at hh; exact hh.symm
  have h2 : ((Arm64.normalizePath p).head? == some bundleDir) = false :=
    hh ▸ beq_false_of_ne fun heq => hb (Option.some.inj heq)
  simp [IsScrubbedPath, h1, h2]

private theorem not_scrubbed_two {p d s : String}
    (hp : Arm64.normalizePath p = [d, s]) (hc : d ≠ "coins") (hb : d ≠ "bundle") :
    IsScrubbedPath p = false :=
  not_scrubbed_of_head (by simp [hp]) hc hb

theorem isScrubbedPath_encodeDir (P : PEParams) (st : PqParty) :
    ∀ f ∈ encodeDir P st, IsScrubbedPath f.1 = false := by
  intro f hf; unfold encodeDir at hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_flatten, or_assoc] at hf
  rcases hf with rfl | rfl | rfl | h | h | ⟨⟨i, _⟩, _, rfl⟩ | ⟨⟨i, _⟩, _, rfl⟩ | ⟨⟨i, _⟩, _, rfl⟩ |
    ⟨l, ⟨⟨i, _, _⟩, _, rfl⟩, hl⟩
  · dsimp only; decide
  · dsimp only; decide
  · dsimp only; decide
  · cases hp : st.peerId <;> simp [hp] at h; subst h; dsimp only; cases st.party <;> decide
  · cases hs : st.session <;> simp [hs] at h; subst h; dsimp only; cases st.party <;> decide
  · dsimp only
    exact not_scrubbed_two (by simpa [signedPreKeyFile] using normalizePath_dir_nat_suf (d := "signed-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
  · dsimp only
    exact not_scrubbed_two (by simpa [oneTimePreKeyFile] using normalizePath_dir_nat_suf (d := "one-time-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
  · dsimp only
    exact not_scrubbed_two (by simpa [oneTimeKyberPreKeyFile] using normalizePath_dir_nat_suf (d := "one-time-kyber-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
  · rcases List.mem_cons.mp hl with rfl | hl'
    · dsimp only
      exact not_scrubbed_two (by simpa [lastResortKyberPreKeyFile] using normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)
    · rw [List.mem_singleton.mp hl']; dsimp only
      exact not_scrubbed_two (by simpa [baseKeysFile] using normalizePath_dir_nat_suf (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") i.toNat (by decide) (by decide) (by decide) (by decide)) (by decide) (by decide)

theorem isScrubbedPath_bundle_files (b : PublicBundle) :
    ∀ f ∈ b.files bundleDir, IsScrubbedPath f.1 = true := by
  intro f hf; unfold PublicBundle.files at hf
  rcases ho : b.oneTime with _ | ⟨_, _⟩ <;>
    simp only [ho, List.append_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hf
  · rcases hf with rfl | rfl | rfl | rfl <;> (dsimp only; decide)
  · rcases hf with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)

private theorem optFold_ne_none_of_init :
    ∀ (files : List (String × HwBytes)) (p : String) (init : Option HwBytes), init ≠ none →
      files.foldl (fun acc kv =>
        if Arm64.normalizePath p == Arm64.normalizePath kv.1 then some kv.2 else acc) init ≠ none
  | [], _, _, h => h
  | _ :: tl, p, init, h => by
    simp only [List.foldl_cons]
    split_ifs <;> [exact optFold_ne_none_of_init tl p _ (by simp); exact optFold_ne_none_of_init tl p init h]

theorem filesOf_ne_none_of_mem {files : List (String × HwBytes)} (hreg : RegularFileList files)
    {p : String} {g : String × HwBytes} (hmem : g ∈ files)
    (heq : Arm64.normalizePath p = Arm64.normalizePath g.1) :
    filesOf files p ≠ none := by
  rw [filesOf_eq_optFold hreg]
  induction files with
  | nil => cases hmem
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp only [beq_iff_eq.mpr heq, ↓reduceIte]
      exact optFold_ne_none_of_init tl p (some g.2) (by simp)
    · split_ifs <;> [exact optFold_ne_none_of_init tl p (some hd.2) (by simp);
        exact ih (fun x hx => hreg x (List.mem_cons_of_mem _ hx)) htl]

theorem encodeDir_sub_of_fields {P : PEParams} {st st' : PqParty}
    (hp : st'.party = st.party) (hpeer : st'.peerId = st.peerId) (hsess : st'.session.isSome = true)
    (hsig : st'.signed.map Prod.fst = st.signed.map Prod.fst)
    (hot : st'.oneTime.map Prod.fst = st.oneTime.map Prod.fst)
    (hkot : st.kyberOneTime = []) (hkot' : st'.kyberOneTime = [])
    (hklr : st'.kyberLastResort.map Prod.fst = st.kyberLastResort.map Prod.fst) :
    ∀ f ∈ encodeDir P st, ∃ g ∈ encodeDir P st', f.1 = g.1 := by
  intro f hf; unfold encodeDir at hf
  simp only [hkot, List.map_nil, List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map, List.mem_flatten, or_assoc] at hf
  rcases hf with rfl | rfl | rfl | h | h | h | h | h
  · refine ⟨(addressFile, CryptoVerification.SignalSession.textBytes (partyAddress st'.party).text), ?_, rfl⟩
    unfold encodeDir; simp only [List.cons_append]; exact List.mem_cons_self
  · refine ⟨(identityKeyPairFile, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
        ⟨djbKey (keyPairOf P.C st'.me.idPriv).publicKey.bytes, st'.me.idPriv.toList⟩), ?_, rfl⟩
    unfold encodeDir; simp only [List.cons_append]; exact List.mem_cons_of_mem _ List.mem_cons_self
  · refine ⟨(registrationIdFile, CryptoVerification.SignalSession.le32 st'.me.regId), ?_, rfl⟩
    unfold encodeDir; simp only [List.cons_append]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · cases hpi : st.peerId with
    | none => simp [hpi] at h
    | some val =>
      simp only [hpi, List.mem_singleton] at h; subst h
      refine ⟨(identityFile (partyAddressName st'.party.other), val.serialize), ?_, by simp [hp]⟩
      unfold encodeDir; rw [hpeer.trans hpi]; simp only [List.mem_append]
      left; left; left; left; left; right; exact List.mem_singleton.mpr rfl
  · cases hs : st.session with
    | none => simp [hs] at h
    | some _ =>
      simp only [hs, List.mem_singleton] at h; subst h
      obtain ⟨⟨x', g'⟩, hs'⟩ := Option.isSome_iff_exists.mp hsess
      refine ⟨(sessionFile (partyAddress st'.party.other), encodeRecordUnderExtras (fun _ => x') g'), ?_, by simp [hp]⟩
      unfold encodeDir; rw [hs']; simp only [List.mem_append]
      left; left; left; left; right; exact List.mem_singleton.mpr rfl
  · rcases h with ⟨⟨i, _⟩, hm, rfl⟩
    obtain ⟨⟨i', k'⟩, hm', hi⟩ := List.mem_map.mp (hsig ▸ List.mem_map_of_mem (f := Prod.fst) hm)
    dsimp only at hi; subst hi
    refine ⟨(signedPreKeyFile i', signedRecordBytes P.C i' k'), ?_, rfl⟩
    unfold encodeDir; simp only [List.mem_append]; left; left; left; right
    exact List.mem_map.mpr ⟨(i', k'), hm', rfl⟩
  · rcases h with ⟨⟨i, _⟩, hm, rfl⟩
    obtain ⟨⟨i', k'⟩, hm', hi⟩ := List.mem_map.mp (hot ▸ List.mem_map_of_mem (f := Prod.fst) hm)
    dsimp only at hi; subst hi
    refine ⟨(oneTimePreKeyFile i', Option.elim k' [] (oneTimeRecordBytes P.C i')), ?_, rfl⟩
    unfold encodeDir; simp only [List.mem_append]; left; left; right
    exact List.mem_map.mpr ⟨(i', k'), hm', by cases k' <;> rfl⟩
  · rcases h with ⟨l, ⟨⟨i, _, _⟩, hm, rfl⟩, hl⟩
    obtain ⟨⟨i', k', seen'⟩, hm', hi⟩ := List.mem_map.mp (hklr ▸ List.mem_map_of_mem (f := Prod.fst) hm)
    dsimp only at hi; subst hi
    rcases List.mem_cons.mp hl with rfl | hl'
    · refine ⟨(lastResortKyberPreKeyFile i', kyberRecordBytes i' k'), ?_, rfl⟩
      unfold encodeDir; rw [hkot']; simp only [List.mem_append]; right
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, hm', rfl⟩, by simp⟩
    · rw [List.mem_singleton.mp hl']
      refine ⟨(baseKeysFile i', baseKeysBytes seen'), ?_, rfl⟩
      unfold encodeDir; rw [hkot']; simp only [List.mem_append]; right
      exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨_, hm', rfl⟩, by simp⟩

theorem scrub_filesOf_pqInputs_reject (P : PEParams) (st : PqParty) (cmd : Cmd)
    (extra : List (String × HwBytes)) (coins stdin : HwBytes)
    (hextra_reg : RegularFileList extra) (hextra_scr : ∀ f ∈ extra, IsScrubbedPath f.1 = true) :
    scrub (filesOf (pqInputs P st cmd extra coins stdin).files) = filesOf (encodeDir P st) := by
  funext p
  have hex_reg : RegularFileList (extra ++ [(coinsFile, coins)]) :=
    hextra_reg.append (regularFile_root (by decide) (by decide) (by decide) (by decide))
  have hex_scr : ∀ f ∈ extra ++ [(coinsFile, coins)], IsScrubbedPath f.1 = true := fun f hf =>
    (List.mem_append.mp hf).elim (hextra_scr f) (fun h => by rw [List.mem_singleton.mp h]; dsimp only; decide)
  change (if IsScrubbedPath p then none
    else filesOf (encodeDir P st ++ extra ++ [(coinsFile, coins)]) p) = filesOf (encodeDir P st) p
  cases hs : IsScrubbedPath p
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_assoc]
    rw [filesOf_append_of_regular (regularFileList_encodeDir P st) hex_reg p]
    have hnone : filesOf (extra ++ [(coinsFile, coins)]) p = none :=
      filesOf_eq_none_of_forall_ne hex_reg fun f hf heq => by
        have := (isScrubbedPath_congr heq).symm.trans hs; rw [hex_scr f hf] at this; cases this
    simp [hnone]
  · simp only [↓reduceIte]; symm
    exact filesOf_eq_none_of_forall_ne (regularFileList_encodeDir P st) fun f hf heq => by
      have := (isScrubbedPath_congr heq).symm.trans hs
      rw [isScrubbedPath_encodeDir P st f hf] at this; cases this

theorem scrub_filesOf_pqInputs_accept (P : PEParams) (st st' : PqParty) (cmd : Cmd)
    (extra : List (String × HwBytes)) (coins stdin : HwBytes)
    (hextra_reg : RegularFileList extra) (hextra_scr : ∀ f ∈ extra, IsScrubbedPath f.1 = true)
    (hsub : ∀ f ∈ encodeDir P st, ∃ g ∈ encodeDir P st', f.1 = g.1) :
    scrub (filesOf ((pqInputs P st cmd extra coins stdin).files ++ encodeDir P st')) =
      filesOf (encodeDir P st') := by
  funext p
  have hi_reg : RegularFileList (pqInputs P st cmd extra coins stdin).files :=
    ((regularFileList_encodeDir P st).append hextra_reg).append
      (regularFile_root (by decide) (by decide) (by decide) (by decide))
  have hrej := congrFun (scrub_filesOf_pqInputs_reject P st cmd extra coins stdin hextra_reg hextra_scr) p
  change (if IsScrubbedPath p then none else _) = _ at hrej ⊢
  cases hs : IsScrubbedPath p
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hrej ⊢
    rw [filesOf_append_of_regular hi_reg (regularFileList_encodeDir P st') p, hrej]
    cases h' : filesOf (encodeDir P st') p with
    | some _ => rfl
    | none =>
      simp only [Option.none_or]
      cases h0 : filesOf (encodeDir P st) p with
      | none => rfl
      | some _ =>
        obtain ⟨f, hf, hfn, _⟩ := mem_of_filesOf_eq_some (regularFileList_encodeDir P st) h0
        obtain ⟨g, hg, hfg⟩ := hsub f hf
        exact absurd h' (filesOf_ne_none_of_mem (regularFileList_encodeDir P st') hg
          (hfn.symm.trans (congrArg Arm64.normalizePath hfg)))
  · simp only [↓reduceIte]; symm
    exact filesOf_eq_none_of_forall_ne (regularFileList_encodeDir P st') fun f hf heq => by
      have := (isScrubbedPath_congr heq).symm.trans hs
      rw [isScrubbedPath_encodeDir P st' f hf] at this; cases this

theorem scrub_agreeExcept_pqInputs_accept {r : ProtocolSetup} (P : PEParams) (st st' : PqParty)
    (cmd : Cmd) (extra : List (String × HwBytes)) (coins stdin : HwBytes) (files : DirectorySnapshot)
    (hp : st.party = partyOf r r.bob)
    (hextra_reg : RegularFileList extra) (hextra_scr : ∀ f ∈ extra, IsScrubbedPath f.1 = true)
    (hsub : ∀ f ∈ encodeDir P st, ∃ g ∈ encodeDir P st', f.1 = g.1)
    (hag : ∀ q, Arm64.normalizePath q ≠ Arm64.normalizePath (sessionFile (partyAddress st.party.other)) →
      files q = filesOf ((pqInputs P st cmd extra coins stdin).files ++ encodeDir P st') q) :
    ∀ q, SamePath q (sessionPathOf r r.bob) = false →
      scrub files q = filesOf (encodeDir P st') q := by
  intro q hq
  have hacc := congrFun (scrub_filesOf_pqInputs_accept P st st' cmd extra coins stdin hextra_reg hextra_scr hsub) q
  have hne : Arm64.normalizePath q ≠ Arm64.normalizePath (sessionFile (partyAddress st.party.other)) := by
    rw [hp, ← sessionPathOf_eq_sessionFile]; exact beq_eq_false_iff_ne.mp hq
  change (if IsScrubbedPath q then none else _) = _ at hacc ⊢
  cases hs : IsScrubbedPath q <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at hacc ⊢
  · exact (hag q hne).trans hacc
  · exact hacc

/-! ## Model-step preservation of `PqPartyInv` -/

theorem peerId_eq_of_trusts {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {p : Participant} {st : PqParty} {d : DirectorySnapshot} {k : IdentityKey}
    (hinv : PqPartyInv interp P r accepted p st d) (ht : st.trusts k = true) :
    some k = st.peerId := by
  rw [hinv.peerId_eq]
  unfold PqParty.trusts at ht
  rw [hinv.peerId_eq] at ht
  exact congrArg some (of_decide_eq_true ht).symm

private theorem initiateState_party {X : UnreachedPqxdhPrimitives} {P : PEParams} {pty : Party} {me : LocalIdentity}
    {b : PreKeyBundleFields} {t : List.Vector (BitVec 8) initiateTapeLen} {x : RecordExtras}
    {g : GhostState HwBytes} (h : initiateState X P pty me b t = some (x, g)) :
    g.party = pty := by
  unfold initiateState at h
  split at h <;> [cases h; (dsimp only at h; split at h <;> [cases h;
    (rcases Option.some.inj h with ⟨_, rfl⟩; rfl)])]

private theorem recvPrekeyState_party {X : UnreachedPqxdhPrimitives} {P : PEParams} {pty : Party} {me : LocalIdentity}
    {k : ResponderPreKeySecrets} {m : PreKeyMessageFields} {rc : BitVec 256} {x : RecordExtras} {g : GhostState HwBytes}
    {pt : HwBytes} (h : recvPrekeyState X P pty me k m rc = some (some (x, g, pt))) :
    g.party = pty := by
  unfold recvPrekeyState at h
  split at h
  · cases h
  · dsimp only at h; split_ifs at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rcases Option.some.inj (Option.some.inj h) with ⟨_, rfl, _⟩; rfl
        · cases h
        · cases Option.some.inj h

theorem keysFor_bob_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {stB : PqParty} {d : DirectorySnapshot} {m : PreKeyMessageFields} {k : ResponderPreKeySecrets}
    (hne : r.alice ≠ r.bob) (hB : PqPartyInv interp P r accepted r.bob stB d)
    (hk : preKeysNamedBy stB m = some k) :
    m.spkId = r.spkId ∧ m.kpkId = r.kpkId ∧
    k.spkId = r.spkId ∧ k.spkPriv = bytesToVec 32 (secretBytes r 2) ∧
    k.kpkId = r.kpkId ∧ k.kpkPub = bytesToVec 1568 (r.opaqueBytes (setupPublic r 6)) ∧
    k.kpkSec = bytesToVec 3168 (r.kyberSecB.drop 1) ∧
    ((m.opkId = none ∧ k.opk = none) ∨
     (r.withOpk = true ∧ m.opkId = some r.opkId ∧
      k.opk = some (r.opkId, bytesToVec 32 (secretBytes r 6)) ∧
      stB.oneTime = [(r.opkId, some (bytesToVec 32 (secretBytes r 6)))])) := by
  obtain ⟨hsig, hkot, hot, ⟨seen, hklr, _, _⟩⟩ := hB.bob_stores hne.symm
  unfold preKeysNamedBy at hk; rw [hsig, hkot, hklr] at hk; simp only [List.lookup] at hk
  cases hsp : m.spkId == r.spkId <;> [simp [hsp] at hk; skip]
  cases hkp : m.kpkId == r.kpkId <;> [simp [hsp, hkp] at hk; skip]
  simp only [hsp, hkp, Option.map_some] at hk
  cases hop : m.opkId with
  | none =>
    rw [hop] at hk; simp only [Option.map_some, Option.some.injEq] at hk; subst hk
    exact ⟨eq_of_beq hsp, eq_of_beq hkp, eq_of_beq hsp, rfl, eq_of_beq hkp, rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
  | some j =>
    rw [hop] at hk
    rcases hot with ⟨_, hot_nil⟩ | ⟨hyes, hot_some | hot_none⟩
    · simp [hot_nil] at hk
    · rw [hot_some] at hk; simp only [List.lookup] at hk
      cases hj : j == r.opkId <;> [simp [hj] at hk; skip]
      simp only [hj, Option.map_some, Option.some.injEq] at hk; subst hk
      exact ⟨eq_of_beq hsp, eq_of_beq hkp, eq_of_beq hsp, rfl, eq_of_beq hkp, rfl, rfl,
        Or.inr ⟨hyes, congrArg some (eq_of_beq hj), (eq_of_beq hj) ▸ rfl, hot_some⟩⟩
    · rw [hot_none] at hk; cases hj : j == r.opkId <;> simp [List.lookup, hj] at hk

private theorem pqPartyInv_update_session {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {p : Participant} {st : PqParty} {d : DirectorySnapshot}
    {k : IdentityKey} {x : RecordExtras} {g' : GhostState HwBytes}
    (hinv : PqPartyInv interp P r accepted p st d) (ht : st.trusts k = true)
    (hreach : (∃ g₀, ReachablePqxdhSession P st.me x g₀ ∧ g₀.party = g'.party ∧ g₀.session = g'.session) ∧
      g'.party = st.party) :
    PqPartyInv interp P r accepted p { st with peerId := some k, session := some (x, g') }
      (filesOf (encodeDir P { st with peerId := some k, session := some (x, g') })) ∧
    (∀ f ∈ encodeDir P st,
      ∃ g ∈ encodeDir P { st with peerId := some k, session := some (x, g') },
        f.1 = g.1) := by
  have hpeer := peerId_eq_of_trusts hinv ht
  have hkot := (pqPartyInv_store_bounds hinv).2.2.1
  refine ⟨⟨hinv.1, hinv.2, hpeer.trans hinv.3, hinv.4, hinv.5, ?_, rfl⟩,
    encodeDir_sub_of_fields rfl hpeer rfl rfl rfl hkot hkot rfl⟩
  intro x₁ g₁ hs₁; rcases Prod.mk.inj (Option.some.inj hs₁) with ⟨rfl, rfl⟩; exact hreach

theorem pqPartyInv_of_pqInitModel {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {p : Participant} {st st' : PqParty} {d : DirectorySnapshot}
    {X : UnreachedPqxdhPrimitives} {b : PreKeyBundleFields} {tape : List.Vector (BitVec 8) initiateTapeLen} {out : HwBytes}
    (hinv : PqPartyInv interp P r accepted p st d)
    (hmod : pqInitModel X P st b tape = some (some (st', out))) :
    out = [] ∧
    PqPartyInv interp P r accepted p st' (filesOf (encodeDir P st')) ∧
    (∀ f ∈ encodeDir P st, ∃ g ∈ encodeDir P st', f.1 = g.1) := by
  unfold pqInitModel at hmod
  cases ht : st.trusts ⟨⟨b.idPub⟩⟩ <;> [simp [ht] at hmod; skip]
  simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod
  cases hi : initiateState X P st.party st.me b tape with
  | none => rw [hi] at hmod; cases hmod
  | some xg =>
    rcases xg with ⟨x, g⟩; rw [hi] at hmod
    rcases Option.some.inj (Option.some.inj hmod) with ⟨rfl, rfl⟩
    exact ⟨rfl, pqPartyInv_update_session hinv ht
      ⟨⟨g, ReachablePqxdhSession.initiate X st.party st.me b tape x g hi, rfl, rfl⟩, initiateState_party hi⟩⟩

theorem pqPartyInv_of_pqSendModel {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {p : Participant} {st st' : PqParty} {d : DirectorySnapshot}
    {m coins out : HwBytes}
    (hinv : PqPartyInv interp P r accepted p st d) (hwf : PqxdhPartyInSpecDomain P st)
    (hmod : pqSendModel P st m coins = some (some (st', out))) :
    PqPartyInv interp P r accepted p st' (filesOf (encodeDir P st')) ∧
    (∀ f ∈ encodeDir P st, ∃ g ∈ encodeDir P st', f.1 = g.1) := by
  unfold pqSendModel at hmod
  cases hsess : st.session with
  | none => rw [hsess] at hmod; cases hmod
  | some xg =>
    rcases xg with ⟨x, g⟩; rw [hsess] at hmod; dsimp only at hmod
    rcases henc : SessionState.messageEncrypt P.C protoSignalCodec (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).sendAddrs g.party) m coins g.session with ⟨err | msg, s⟩
    · rw [henc] at hmod; cases err <;> cases hmod
    · rw [henc] at hmod; dsimp only at hmod
      cases hk : g.session.remoteIdentity with
      | none => rw [hk] at hmod; cases hmod
      | some k =>
        rw [hk] at hmod; dsimp only at hmod
        cases ht : st.trusts k <;> [simp [ht] at hmod; skip]
        simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod
        rcases Option.some.inj (Option.some.inj hmod) with ⟨rfl, rfl⟩
        obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, hgp, hlen_g⟩ := hwf.1 x g hsess
        have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
          unfold encodeRecordUnderExtras at hlen_g ⊢; rwa [hs₀]
        refine pqPartyInv_update_session hinv ht
          ⟨⟨((pqxdhSessionParams P).send g₀ m coins).1, ReachablePqxdhSession.send m coins hR₀ hlen₀, ?_⟩, hgp⟩
        unfold Params.send; change _ ∧ _
        rw [show (pqxdhSessionParams P).C = P.C from rfl,
            show (pqxdhSessionParams P).codec = protoSignalCodec from rfl,
            show (pqxdhSessionParams P).spqr = pqxdhSpqrSession P from rfl, hp₀, hs₀, henc]
        exact ⟨rfl, rfl⟩

theorem pqPartyInv_of_pqRecvWhisperModel {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {p : Participant} {st st' : PqParty} {d : DirectorySnapshot}
    {body out : HwBytes} {rc : BitVec 256}
    (hinv : PqPartyInv interp P r accepted p st d) (hwf : PqxdhPartyInSpecDomain P st)
    (hmod : pqRecvWhisperModel P st body rc = some (some (st', out))) :
    PqPartyInv interp P r accepted p st' (filesOf (encodeDir P st')) ∧
    (∀ f ∈ encodeDir P st, ∃ g ∈ encodeDir P st', f.1 = g.1) := by
  unfold pqRecvWhisperModel at hmod
  cases hsess : st.session with
  | none => rw [hsess] at hmod; cases hmod
  | some xg =>
    rcases xg with ⟨x, g⟩; rw [hsess] at hmod; dsimp only at hmod
    cases htry : SignalMessage.tryFrom protoSignalCodec body with
    | error _ => rw [htry] at hmod; cases hmod
    | ok msg =>
      rw [htry] at hmod; dsimp only at hmod; unfold pqxdhSessionDecryptModel at hmod
      rcases hdec : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
          ((pqxdhSessionParams P).expectedAddrs g.party) msg .whisper rc g.session with ⟨err | pt, s⟩
      · rw [hdec] at hmod; cases err <;> cases hmod
      · rw [hdec] at hmod; dsimp only at hmod
        cases hk : s.remoteIdentity with
        | none => rw [hk] at hmod; cases hmod
        | some k =>
          rw [hk] at hmod; dsimp only at hmod
          cases ht : st.trusts k <;> [simp [ht] at hmod; skip]
          simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod
          rcases Option.some.inj (Option.some.inj hmod) with ⟨rfl, rfl⟩
          obtain ⟨⟨g₀, hR₀, hp₀, hs₀⟩, hgp, hlen_g⟩ := hwf.1 x g hsess
          have hlen₀ : (encodeRecordUnderExtras (fun _ => x) g₀).length < 2 ^ 31 := by
            unfold encodeRecordUnderExtras at hlen_g ⊢; rwa [hs₀]
          have hrcv : ∃ g₁ r_out, (pqxdhSessionParams P).receive g₀ body rc = some (g₁, r_out) ∧
              g₁.party = g.party ∧ g₁.session = s := by
            unfold Params.receive
            rw [show (pqxdhSessionParams P).codec = protoSignalCodec from rfl, htry,
                show (pqxdhSessionParams P).C = P.C from rfl,
                show (pqxdhSessionParams P).spqr = pqxdhSpqrSession P from rfl, hp₀, hs₀]
            dsimp only; rw [hdec]; exact ⟨_, _, rfl, rfl, rfl⟩
          rcases hrcv with ⟨g₁, _, hrcv₁, hp₁, hs₁⟩
          exact pqPartyInv_update_session hinv ht ⟨⟨g₁, ReachablePqxdhSession.recv hR₀ hlen₀ hrcv₁, hp₁, hs₁⟩, hgp⟩

private theorem djbKey_inj {v w : List.Vector (BitVec 8) 32} (h : djbKey v = djbKey w) : v = w :=
  Subtype.ext (List.cons.inj h).2

private theorem removeOpk_fields (st : PqParty) (m : PreKeyMessageFields) :
    (removeOpk st m).party = st.party ∧ (removeOpk st m).me = st.me ∧
    (removeOpk st m).signed = st.signed ∧ (removeOpk st m).kyberOneTime = st.kyberOneTime ∧
    (removeOpk st m).kyberLastResort = st.kyberLastResort := by
  unfold removeOpk; cases m.opkId <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem pqPartyInv_of_pqRecvPrekeyModel_fresh {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {stB st' : PqParty} {d : DirectorySnapshot}
    {X : UnreachedPqxdhPrimitives} {m : PreKeyMessageFields} {rc : BitVec 256} {out : HwBytes}
    (hne : r.alice ≠ r.bob) (hB : PqPartyInv interp P r accepted r.bob stB d)
    (hmod : pqRecvPrekeyModel X P { stB with session := none } m rc =
      some (some (st', out))) :
    djbKey m.baseKey ∉ accepted ∧
    PqPartyInv interp P r (accepted ++ [djbKey m.baseKey]) r.bob st'
      (filesOf (encodeDir P st')) ∧
    (∀ f ∈ encodeDir P stB, ∃ g ∈ encodeDir P st', f.1 = g.1) := by
  unfold pqRecvPrekeyModel at hmod
  cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
  | error _ => rw [htry] at hmod; cases hmod
  | ok inner =>
    rw [htry] at hmod; dsimp only at hmod
    rw [show ({ stB with session := none } : PqParty).trusts ⟨⟨m.idPub⟩⟩ = stB.trusts ⟨⟨m.idPub⟩⟩ from rfl] at hmod
    cases ht : stB.trusts ⟨⟨m.idPub⟩⟩ <;> [simp [ht] at hmod; skip]
    simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hmod
    rw [show preKeysNamedBy { stB with session := none } m = preKeysNamedBy stB m from rfl] at hmod
    cases hkf : preKeysNamedBy stB m with
    | none => rw [hkf] at hmod; cases hmod
    | some k =>
      rw [hkf] at hmod; dsimp only at hmod
      obtain ⟨hspk_id, hkpk_id, _, _, _, _, _, hopk_case⟩ := keysFor_bob_of_pqPartyInv hne hB hkf
      rcases hrs : recvPrekeyState X P stB.party stB.me k m rc with _ | (_ | ⟨x', g', pt⟩)
      · rw [hrs] at hmod; cases hmod
      · rw [hrs] at hmod; cases hmod
      · rw [hrs] at hmod; dsimp only at hmod
        obtain ⟨hsig, hkot, hot_inv, ⟨seen, hklr, hseen_spk, hseen_acc⟩⟩ := hB.bob_stores hne.symm
        let st1 : PqParty := { stB with session := none, kyberOneTime := [], kyberLastResort :=
          [(r.kpkId, ⟨bytesToVec 1568 (r.opaqueBytes (setupPublic r 6)),
            bytesToVec 3168 (r.kyberSecB.drop 1),
            bytesToVec 64 (r.opaqueBytes (setupPublic r 7)), 0⟩, seen ++ [(r.spkId, m.baseKey)])] }
        have hmk : markKyberUsed { stB with session := none } m =
            if 37 * seen.length > fileCapBytes ∨ (r.spkId, m.baseKey) ∈ seen then none else some st1 := by
          unfold markKyberUsed
          simp only [hkot, hklr, hkpk_id, hspk_id, List.lookup, beq_self_eq_true,
            List.map_cons, List.map_nil, ↓reduceIte]
          rfl
        rw [hmk] at hmod
        split_ifs at hmod with hseen_or
        · cases hmod
        · have hseen_mem : (r.spkId, m.baseKey) ∉ seen := fun hm => hseen_or (Or.inr hm)
          rcases Option.some.inj (Option.some.inj hmod) with ⟨rfl, rfl⟩
          obtain ⟨rf_pty, rf_me, rf_sig, rf_kot, rf_klr⟩ := removeOpk_fields st1 m
          have hnot_acc : djbKey m.baseKey ∉ accepted := fun hmem => by
            obtain ⟨v, hv, hvs⟩ := (hseen_acc (djbKey m.baseKey)).mp hmem
            exact hseen_mem (djbKey_inj hv ▸ hvs)
          have hpeer := peerId_eq_of_trusts hB ht
          have hot_fst : (removeOpk st1 m).oneTime.map Prod.fst = stB.oneTime.map Prod.fst := by
            rcases hopk_case with ⟨hop_none, _⟩ | ⟨_, hop_some, _, hot_stB⟩
            · simp [st1, removeOpk, hop_none]
            · simp [st1, removeOpk, hop_some, hot_stB]
          refine ⟨hnot_acc, ⟨rf_pty.trans hB.1, rf_me.trans hB.2, hpeer.trans hB.3,
            fun ha => absurd ha.symm hne, ?_, ?_, rfl⟩,
            encodeDir_sub_of_fields rf_pty hpeer rfl (by rw [rf_sig]) hot_fst hkot
              rf_kot (by rw [rf_klr]; simp [st1, hklr])⟩
          · intro _
            refine ⟨rf_sig.trans hsig, rf_kot, ?_,
              ⟨seen ++ [(r.spkId, m.baseKey)], rf_klr,
                fun q hq => (List.mem_append.mp hq).elim (hseen_spk q) fun h2 => by
                  rw [List.mem_singleton.mp h2], ?_⟩⟩
            · rcases hopk_case with ⟨hop_none, _⟩ | ⟨hyes, hop_some, _, hot_stB⟩
              · simpa [st1, removeOpk, hop_none] using hot_inv
              · simp [st1, removeOpk, hop_some, hyes, hot_stB]
            · intro bk; rw [List.mem_append, List.mem_singleton, hseen_acc bk]
              refine ⟨fun h => h.elim (fun ⟨v, hv, hvs⟩ => ⟨v, hv, List.mem_append_left _ hvs⟩)
                  (fun h => h ▸ ⟨m.baseKey, rfl, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩),
                fun ⟨v, hv, hvs⟩ => (List.mem_append.mp hvs).elim (fun h1 => Or.inl ⟨v, hv, h1⟩)
                  (fun h2 => Or.inr (hv.trans (congrArg djbKey (Prod.mk.inj (List.mem_singleton.mp h2)).2)))⟩
          · intro x₀ g₀ hs₀; rcases Prod.mk.inj (Option.some.inj hs₀) with ⟨rfl, rfl⟩
            change _ ∧ g'.party = (removeOpk st1 m).party
            rw [rf_me, rf_pty]
            exact ⟨⟨g', ReachablePqxdhSession.recvPrekey X stB.party stB.me k m rc x' g' out hrs, rfl, rfl⟩,
              recvPrekeyState_party hrs⟩

end Symbolic.Swarm.CREF.Cli
