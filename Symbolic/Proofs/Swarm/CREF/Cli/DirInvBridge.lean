/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.DirBridgeAux
import all Init.Data.Repr
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.RecordBridgeAux
import Symbolic.Proofs.Swarm.CREF.Sem

/-!
# PQXDH Directory Invariants and Projections

Defines the directory invariants `PqPartyInv`, `PqBobInv`, and `PqDirInv` relating `CliTurn`
snapshots and Bob's `.base-keys` replay list to `PqParty` states, and derives `PqxdhPartyInSpecDomain`,
`CliTurn.records`, and `CliTurn.opkUsed` projections.
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

/-! ## Clamping and party projections -/

theorem cliTextBytes_eq_signalTextBytes (s : String) :
    DY.Libsignal.Composed.Refinement.Cli.textBytes s = CryptoVerification.SignalSession.textBytes s := by
  unfold DY.Libsignal.Composed.Refinement.Cli.textBytes
    CryptoVerification.SignalSession.textBytes
    CryptoVerification.LibsignalTripleRatchetRepr.utf8
  refine List.map_congr_left fun b _ => ?_
  apply BitVec.eq_of_toNat_eq; simp

theorem clamp_toList_eq_clampScalar (v : List.Vector (BitVec 8) 32) :
    DY.Libsignal.Composed.Refinement.clamp v.toList = (Ratchet.clampScalar v).toList := by
  rcases v with ⟨l, hl⟩
  have hrhs : (Ratchet.clampScalar ⟨l, hl⟩).toList =
      (l.set 0 (l[0] &&& 0xf8#8)).set 31 ((l[31] &&& 0x7f#8) ||| 0x40#8) := rfl
  rw [List.Vector.toList_mk, hrhs]
  refine List.ext_getElem (by simp [DY.Libsignal.Composed.Refinement.clamp, hl]) fun i h1 _ => ?_
  simp only [DY.Libsignal.Composed.Refinement.clamp, hl, ↓reduceIte, List.getElem_mapIdx,
    List.getElem_set, DY.Libsignal.Composed.Refinement.clampByte]
  by_cases h0 : i = 0
  · subst h0; simp
  · by_cases h31 : i = 31
    · subst h31; simp
    · split_ifs <;> first | rfl | omega

theorem bytesToVec_toList_of_len {n : Nat} {bs : HwBytes} (hlen : bs.length = n) :
    (bytesToVec n bs).toList = bs := by
  change (bs ++ List.replicate n 0#8).take n = bs
  rw [List.take_append_of_le_length (Nat.le_of_eq hlen.symm), List.take_of_length_le (Nat.le_of_eq hlen)]

theorem pubBytes_eq_keyPairOf_of_modelAgree {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) (v : List.Vector (BitVec 8) 32) :
    pubBytes interp v.toList = (keyPairOf P.C v).publicKey.bytes.toList := by
  unfold pubBytes keyPairOf
  rw [clamp_toList_eq_clampScalar v, hagree.2.2.2.2.1 (Ratchet.clampScalar v), Option.getD_some]

theorem pubBytes_length_of_modelAgree {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) {bs : HwBytes} (hlen : bs.length = 32) :
    (pubBytes interp bs).length = 32 := by
  rw [← bytesToVec_toList_of_len hlen, pubBytes_eq_keyPairOf_of_modelAgree hagree]
  exact (keyPairOf P.C (bytesToVec 32 bs)).publicKey.bytes.2

theorem ecKey_pubBytes_eq_djbKey_keyPairOf {interp : ExternInterpretation} {P : PEParams}
    (hagree : ModelAgree interp P) {bs : HwBytes} (hlen : bs.length = 32) :
    ecKey (pubBytes interp bs) = djbKey (keyPairOf P.C (bytesToVec 32 bs)).publicKey.bytes := by
  conv_lhs => rw [← bytesToVec_toList_of_len hlen, pubBytes_eq_keyPairOf_of_modelAgree hagree]
  rfl

/-- Party tag corresponding to participant `p` in `r` (`.A` for `r.alice`, `.B` otherwise). -/
def partyOf (r : ProtocolSetup) (p : Participant) : Party := if p = r.alice then .A else .B

@[simp] theorem partyOf_alice (r : ProtocolSetup) : partyOf r r.alice = .A := by simp [partyOf]
theorem partyOf_bob {r : ProtocolSetup} (hne : r.alice ≠ r.bob) : partyOf r r.bob = .B := by
  simp [partyOf, hne.symm]

@[simp] theorem addrOf_eq_addrE (r : ProtocolSetup) (p : Participant) :
    addrOf r p = partyAddress (partyOf r p) := by
  unfold addrOf nameOf partyOf partyAddress aliceUuid bobUuid partyAddressName; split_ifs <;> rfl

@[simp] theorem peerNameOf_eq_nameE_other (r : ProtocolSetup) (p : Participant) :
    peerNameOf r p = partyAddressName (partyOf r p).other := by
  unfold peerNameOf partyOf aliceUuid bobUuid partyAddressName Party.other; split_ifs <;> rfl

@[simp] theorem peerOf_eq_addrE_other (r : ProtocolSetup) (p : Participant) :
    peerOf r p = partyAddress (partyOf r p).other := by unfold peerOf partyAddress; rw [peerNameOf_eq_nameE_other]

@[simp] theorem sessionPathOf_eq_sessionFile (r : ProtocolSetup) (p : Participant) :
    sessionPathOf r p = sessionFile (partyAddress (partyOf r p).other) := by
  unfold sessionPathOf; rw [peerOf_eq_addrE_other]

theorem secretBytes_0_length {r : ProtocolSetup} (hr : ProtocolSetupWF r) : (secretBytes r 0).length = 32 := by
  have hmem : (0, 32) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1]; simp
  simpa [secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1] using hr.2.1 (0, 32) hmem
theorem secretBytes_1_length {r : ProtocolSetup} (hr : ProtocolSetupWF r) : (secretBytes r 1).length = 32 := by
  have hmem : (5, 32) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1]; simp
  simpa [secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1] using hr.2.1 (5, 32) hmem
theorem secretBytes_2_length {r : ProtocolSetup} (hr : ProtocolSetupWF r) : (secretBytes r 2).length = 32 := by
  have hmem : (10, 32) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1]; simp
  simpa [secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1] using hr.2.1 (10, 32) hmem
theorem secretBytes_6_length {r : ProtocolSetup} (hr : ProtocolSetupWF r) (hopk : r.withOpk = true) :
    (secretBytes r 6).length = 32 := by
  have hmem : (22, 32) ∈ setupRandomsAt r := by rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1, hopk]; simp
  simpa [secretBytes, Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hr.1, hopk] using hr.2.1 (22, 32) hmem
theorem idSecret_length {r : ProtocolSetup} (hr : ProtocolSetupWF r) (p : Participant) :
    (idSecret r p).length = 32 := by
  unfold idSecret; split_ifs <;> [exact secretBytes_0_length hr; exact secretBytes_1_length hr]
theorem peerIdSecret_length {r : ProtocolSetup} (hr : ProtocolSetupWF r) (p : Participant) :
    (peerIdSecret r p).length = 32 := by
  unfold peerIdSecret; split_ifs <;> [exact secretBytes_1_length hr; exact secretBytes_0_length hr]

private theorem extractLsb'_bytesToKey32 :
    ∀ (bs : HwBytes) (j : Nat) (hj : j < bs.length), j < 32 →
      (CryptoGames.HKDF.bytesToKey32 bs).extractLsb' (8 * j) 8 = bs[j]
  | [], _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | _ :: _, 0, _, _ => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [CryptoGames.HKDF.bytesToKey32, hi]; omega
  | b :: rest, j + 1, hj, _ => by
    have hprev := extractLsb'_bytesToKey32 rest j (Nat.lt_of_succ_lt_succ hj) (by omega)
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hprev_i := congrArg (fun v => v.getLsbD i) hprev
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      CryptoGames.HKDF.bytesToKey32, BitVec.zeroExtend] at hprev_i
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      CryptoGames.HKDF.bytesToKey32, List.foldr_cons, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft, BitVec.zeroExtend, BitVec.getLsbD_setWidth, List.getElem_cons_succ]
    simp only [show 8 * (j + 1) + i < 256 by omega, show ¬ (8 * (j + 1) + i < 8) by omega,
      show 8 * (j + 1) + i - 8 = 8 * j + i by omega,
      BitVec.getLsbD_of_ge b (8 * (j + 1) + i) (by omega), decide_true, decide_false,
      Bool.true_and, Bool.or_false]
    exact hprev_i

theorem keyToBytes32_bytesToKey32 {bs : HwBytes} (hlen : bs.length = 32) :
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 bs) = bs := by
  refine List.ext_getElem (by simp [CryptoGames.HMAC.keyToBytes32, hlen]) fun j _ hj2 => ?_
  simpa only [CryptoGames.HMAC.keyToBytes32, List.getElem_ofFn] using
    extractLsb'_bytesToKey32 bs j hj2 (hlen ▸ hj2)

/-! ## Directory invariants and projections -/

/-- Per-party directory invariant coupling `d : Dir` (`filesOf (encodeDir P st)`) to
`st : PqParty` and Bob's `.base-keys` replay list to `accepted : List HwBytes`. -/
structure PqPartyInv (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (accepted : List HwBytes) (p : Participant) (st : PqParty) (d : DirectorySnapshot) : Prop where
  party_eq : st.party = partyOf r p
  me_eq : st.me = ⟨bytesToVec 32 (idSecret r p), regIdOf r p⟩
  peerId_eq : st.peerId = some ⟨⟨bytesToVec 32 (pubBytes interp (peerIdSecret r p))⟩⟩
  alice_stores : p = r.alice →
    st.signed = [] ∧ st.oneTime = [] ∧ st.kyberOneTime = [] ∧ st.kyberLastResort = []
  bob_stores : p ≠ r.alice →
    st.signed = [(r.spkId, ⟨bytesToVec 32 (secretBytes r 2),
      bytesToVec 64 (r.opaqueBytes (setupPublic r 5)), 0⟩)] ∧
    st.kyberOneTime = [] ∧
    ((r.withOpk = false ∧ st.oneTime = []) ∨
     (r.withOpk = true ∧
       (st.oneTime = [(r.opkId, some (bytesToVec 32 (secretBytes r 6)))] ∨
        st.oneTime = [(r.opkId, none)]))) ∧
    ∃ seen,
      st.kyberLastResort = [(r.kpkId,
        ⟨bytesToVec 1568 (r.opaqueBytes (setupPublic r 6)),
         bytesToVec 3168 (r.kyberSecB.drop 1),
         bytesToVec 64 (r.opaqueBytes (setupPublic r 7)), 0⟩, seen)] ∧
      (∀ q ∈ seen, q.1 = r.spkId) ∧
      (∀ bk : HwBytes, bk ∈ accepted ↔
        ∃ v : List.Vector (BitVec 8) 32, bk = djbKey v ∧ (r.spkId, v) ∈ seen)
  session_reach : ∀ x g, st.session = some (x, g) →
    (∃ g₀, ReachablePqxdhSession P st.me x g₀ ∧ g₀.party = g.party ∧ g₀.session = g.session) ∧
    g.party = st.party
  dir_eq : d = filesOf (encodeDir P st)

/-- Responder directory invariant accounting for `bobOff` quarantine: exact `PqPartyInv` when
`bobOff = false`, and agreement with some `d₀` satisfying `PqPartyInv` at every path except
`sessionPathOf r r.bob` when `bobOff = true`. -/
def PqBobInv (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (accepted : List HwBytes) (bobOff : Bool) (stB : PqParty) (d : DirectorySnapshot) : Prop :=
  if bobOff then
    ∃ d₀, PqPartyInv interp P r accepted r.bob stB d₀ ∧
      ∀ q, SamePath q (sessionPathOf r r.bob) = false → d q = d₀ q
  else
    PqPartyInv interp P r accepted r.bob stB d

/-- Two-party CLI directory invariant coupling `t : CliTurn` to `accepted : List HwBytes`. -/
def PqDirInv (interp : ExternInterpretation) (P : PEParams) (r : ProtocolSetup)
    (t : CliTurn) (accepted : List HwBytes) : Prop :=
  (∃ stA, PqPartyInv interp P r accepted r.alice stA (t.dirs r.alice)) ∧
  (∃ stB, PqBobInv interp P r accepted t.bobOff stB (t.dirs r.bob)) ∧
  (∀ p, p ≠ r.alice → p ≠ r.bob → t.dirs p = fun _ => none)

theorem pqPartyInv_alice_accepted_iff {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {acc₁ acc₂ : List HwBytes} {st : PqParty} {d : DirectorySnapshot} :
    PqPartyInv interp P r acc₁ r.alice st d ↔ PqPartyInv interp P r acc₂ r.alice st d := by
  constructor <;> (intro h; exact ⟨h.1, h.2, h.3, h.4, fun hne => absurd rfl hne, h.6, h.7⟩)

theorem optFold_eq_none_of_forall_ne :
    ∀ (files : List (String × HwBytes)) (p : String) (init : Option HwBytes),
      (∀ f ∈ files, (Arm64.normalizePath p == Arm64.normalizePath f.1) = false) →
      files.foldl (fun acc kv =>
        if Arm64.normalizePath p == Arm64.normalizePath kv.1 then some kv.2 else acc) init = init
  | [], _, init, _ => rfl
  | f :: tl, p, init, h => by
    simp only [List.foldl_cons, h f (List.mem_cons_self ..), Bool.false_eq_true, ↓reduceIte]
    exact optFold_eq_none_of_forall_ne tl p init fun g hg => h g (List.mem_cons_of_mem _ hg)

theorem filesOf_eq_none_of_forall_ne {files : List (String × HwBytes)} (hreg : RegularFileList files)
    {p : String} (hne : ∀ f ∈ files, Arm64.normalizePath p ≠ Arm64.normalizePath f.1) :
    filesOf files p = none := by
  rw [filesOf_eq_optFold hreg]
  exact optFold_eq_none_of_forall_ne files p none fun f hf => beq_false_of_ne (hne f hf)

theorem filesOf_eq_some_of_mem_nodup {files : List (String × HwBytes)} (hreg : RegularFileList files)
    (hnd : (files.map fun f => Arm64.normalizePath f.1).Nodup)
    {p q : String} {b : HwBytes} (hmem : (q, b) ∈ files)
    (heq : Arm64.normalizePath p = Arm64.normalizePath q) :
    filesOf files p = some b := by
  rw [filesOf_eq_optFold hreg]
  induction files with
  | nil => cases hmem
  | cons hd tl ih =>
    have hreg_tl : RegularFileList tl := fun f hf => hreg f (List.mem_cons_of_mem _ hf)
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp only [List.foldl_cons, heq, beq_self_eq_true, ↓reduceIte]
      apply optFold_eq_none_of_forall_ne tl q (some b)
      intro f hf; apply beq_false_of_ne
      intro hcontra; exact hnd.1 (hcontra ▸ List.mem_map_of_mem (f := fun x => Arm64.normalizePath x.1) hf)
    · have hneq : (Arm64.normalizePath p == Arm64.normalizePath hd.1) = false := by
        apply beq_false_of_ne; rw [heq]; intro hcontra
        exact hnd.1 (hcontra.symm ▸ List.mem_map_of_mem (f := fun x => Arm64.normalizePath x.1) htl)
      simp only [List.foldl_cons, hneq, Bool.false_eq_true, ↓reduceIte]
      exact ih hreg_tl hnd.2 htl

theorem baseKeysFile_norm_ne_lr (i j : BitVec 32) :
    Arm64.normalizePath (lastResortKyberPreKeyFile i) ≠ Arm64.normalizePath (baseKeysFile j) := by
  intro h
  have h1 : Arm64.normalizePath (lastResortKyberPreKeyFile i) =
      ["last-resort-kyber-pre-keys", toString i.toNat] := by
    simpa [lastResortKyberPreKeyFile] using normalizePath_dir_nat_suf
      (d := "last-resort-kyber-pre-keys") (suf := "") i.toNat (by decide) (by decide) (by decide) (by decide)
  have h2 : Arm64.normalizePath (baseKeysFile j) =
      ["last-resort-kyber-pre-keys", toString j.toNat ++ ".base-keys"] := by
    simpa [baseKeysFile] using normalizePath_dir_nat_suf
      (d := "last-resort-kyber-pre-keys") (suf := ".base-keys") j.toNat
      (by decide) (by decide) (by decide) (by decide)
  have hs : toString i.toNat = toString j.toNat ++ ".base-keys" :=
    (List.cons.inj ((List.cons.inj (h1.symm.trans (h.trans h2))).2)).1
  have hdot : '.' ∈ (toString i.toNat).toList := by
    rw [hs, String.toList_append]; exact List.mem_append_right _ (by decide)
  exact (toString_nat_seg i.toNat).2.1 hdot

theorem head_norm_dir_nat_suf (d suf : String) (n : Nat)
    (hd1 : '/' ∉ d.toList) (hd2 : d.isEmpty = false) (hd3 : (d != ".") = true)
    (hs1 : '/' ∉ suf.toList) :
    (Arm64.normalizePath (d ++ "/" ++ toString n ++ suf)).head? = some d := by
  rw [normalizePath_dir_nat_suf n hd1 hd2 hd3 hs1]; rfl

private theorem nodup_append_of_head_in {l₁ l₂ : List Arm64.FsPath} {s₁ s₂ : List String}
    (h₁ : l₁.Nodup ∧ ∀ p ∈ l₁, ∃ t ∈ s₁, p.head? = some t)
    (h₂ : l₂.Nodup ∧ ∀ q ∈ l₂, ∃ t ∈ s₂, q.head? = some t)
    (hdisj : ∀ t ∈ s₁, t ∉ s₂) :
    (l₁ ++ l₂).Nodup ∧ ∀ p ∈ l₁ ++ l₂, ∃ t ∈ s₁ ++ s₂, p.head? = some t := by
  refine ⟨List.nodup_append.mpr ⟨h₁.1, h₂.1, fun p hp q hq heq => ?_⟩, fun p hp => ?_⟩
  · obtain ⟨t₁, ht₁, hp₁⟩ := h₁.2 p hp
    obtain ⟨t₂, ht₂, hq₂⟩ := h₂.2 q hq
    rw [heq, hq₂] at hp₁
    exact hdisj t₁ ht₁ ((Option.some.inj hp₁) ▸ ht₂)
  · rcases List.mem_append.mp hp with hp₁ | hp₂
    · obtain ⟨t, ht, hp'⟩ := h₁.2 p hp₁; exact ⟨t, List.mem_append_left _ ht, hp'⟩
    · obtain ⟨t, ht, hp'⟩ := h₂.2 p hp₂; exact ⟨t, List.mem_append_right _ ht, hp'⟩

def encodeDirHeads (hasSess : Bool) : List String :=
  ["address", "identity-key-pair", "registration-id", "identities"] ++
    (if hasSess then ["sessions"] else []) ++
    ["signed-pre-keys", "one-time-pre-keys", "last-resort-kyber-pre-keys"]

theorem encodeDir_norm_nodup_and_heads (W' : PEParams) (st : PqParty)
    (hsig : st.signed.length ≤ 1) (hot : st.oneTime.length ≤ 1)
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort.length ≤ 1) :
    ((encodeDir W' st).map fun f => Arm64.normalizePath f.1).Nodup ∧
      ∀ p ∈ (encodeDir W' st).map (fun f => Arm64.normalizePath f.1),
        ∃ t ∈ encodeDirHeads st.session.isSome, p.head? = some t := by
  let nf : String × List (BitVec 8) → Arm64.FsPath := fun f => Arm64.normalizePath f.1
  let l0 : List (String × List (BitVec 8)) :=
    [(addressFile, CryptoVerification.SignalSession.textBytes (partyAddress st.party).text),
     (identityKeyPairFile, CryptoVerification.RecordCodecs.IdentityKeyPairStructure.encode
        ⟨djbKey (keyPairOf W'.C st.me.idPriv).publicKey.bytes, st.me.idPriv.toList⟩),
     (registrationIdFile, CryptoVerification.SignalSession.le32 st.me.regId)]
  let l1 : List (String × List (BitVec 8)) :=
    match st.peerId with | some k => [(identityFile (partyAddressName st.party.other), k.serialize)] | none => []
  let l2 : List (String × List (BitVec 8)) :=
    match st.session with | some (x, g) => [(sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g)] | none => []
  let l3 : List (String × List (BitVec 8)) :=
    st.signed.map (fun (i, k) => (signedPreKeyFile i, signedRecordBytes W'.C i k))
  let l4 : List (String × List (BitVec 8)) :=
    st.oneTime.map (fun (i, k) =>
      (oneTimePreKeyFile i, match k with | some sk => oneTimeRecordBytes W'.C i sk | none => []))
  let l5 : List (String × List (BitVec 8)) :=
    (st.kyberLastResort.map fun (i, k, seen) =>
      [(lastResortKyberPreKeyFile i, kyberRecordBytes i k), (baseKeysFile i, baseKeysBytes seen)]).flatten
  have hed : encodeDir W' st = l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 := by
    unfold encodeDir; rw [hkot]
    simp only [l0, l1, l2, l3, l4, l5, List.map_nil, List.append_nil]; rfl
  have h0 : (l0.map nf).Nodup ∧ ∀ p ∈ l0.map nf,
      ∃ t ∈ ["address", "identity-key-pair", "registration-id"], p.head? = some t := by
    dsimp only [l0, nf, List.map]; decide
  have h1 : (l1.map nf).Nodup ∧ ∀ p ∈ l1.map nf, ∃ t ∈ ["identities"], p.head? = some t := by
    dsimp only [l1]; cases st.peerId with
    | none => simp
    | some _ =>
      refine ⟨List.nodup_singleton _, fun p hp => ⟨"identities", by simp, ?_⟩⟩
      rw [List.mem_singleton.mp hp]; dsimp only [nf]; cases st.party <;> decide
  have h2 : (l2.map nf).Nodup ∧ ∀ p ∈ l2.map nf,
      ∃ t ∈ (if st.session.isSome then ["sessions"] else []), p.head? = some t := by
    dsimp only [l2]; cases st.session with
    | none => simp
    | some xg =>
      rcases xg with ⟨_, _⟩
      refine ⟨List.nodup_singleton _, fun p hp => ⟨"sessions", by simp, ?_⟩⟩
      rw [List.mem_singleton.mp hp]; dsimp only [nf]; cases st.party <;> decide
  have h3 : (l3.map nf).Nodup ∧ ∀ p ∈ l3.map nf, ∃ t ∈ ["signed-pre-keys"], p.head? = some t := by
    dsimp only [l3]; cases hs : st.signed with
    | nil => simp
    | cons a tl =>
      cases tl <;> [skip; (rw [hs] at hsig; simp at hsig)]
      rcases a with ⟨i, _⟩
      refine ⟨List.nodup_singleton _, fun p hp => ⟨"signed-pre-keys", by simp, ?_⟩⟩
      rw [List.mem_singleton.mp hp]
      simpa [nf, signedPreKeyFile] using head_norm_dir_nat_suf "signed-pre-keys" "" i.toNat
        (by decide) (by decide) (by decide) (by decide)
  have h4 : (l4.map nf).Nodup ∧ ∀ p ∈ l4.map nf, ∃ t ∈ ["one-time-pre-keys"], p.head? = some t := by
    dsimp only [l4]; cases ho : st.oneTime with
    | nil => simp
    | cons a tl =>
      cases tl <;> [skip; (rw [ho] at hot; simp at hot)]
      rcases a with ⟨i, _⟩
      refine ⟨List.nodup_singleton _, fun p hp => ⟨"one-time-pre-keys", by simp, ?_⟩⟩
      rw [List.mem_singleton.mp hp]
      simpa [nf, oneTimePreKeyFile] using head_norm_dir_nat_suf "one-time-pre-keys" "" i.toNat
        (by decide) (by decide) (by decide) (by decide)
  have h5 : (l5.map nf).Nodup ∧ ∀ p ∈ l5.map nf, ∃ t ∈ ["last-resort-kyber-pre-keys"], p.head? = some t := by
    dsimp only [l5]; cases hk : st.kyberLastResort with
    | nil => simp
    | cons a tl =>
      cases tl <;> [skip; (rw [hk] at hklr; simp at hklr)]
      rcases a with ⟨i, _, _⟩
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
      refine ⟨by simp [nf, baseKeysFile_norm_ne_lr i i], fun p hp => ⟨"last-resort-kyber-pre-keys", by simp, ?_⟩⟩
      rcases List.mem_cons.mp hp with rfl | hp'
      · simpa [nf, lastResortKyberPreKeyFile] using head_norm_dir_nat_suf
          "last-resort-kyber-pre-keys" "" i.toNat (by decide) (by decide) (by decide) (by decide)
      · rw [List.mem_singleton.mp hp']
        simpa [nf, baseKeysFile] using head_norm_dir_nat_suf
          "last-resort-kyber-pre-keys" ".base-keys" i.toNat (by decide) (by decide) (by decide) (by decide)
  have hc1 := nodup_append_of_head_in h0 h1 (by decide)
  have hc2 := nodup_append_of_head_in hc1 h2 (by cases st.session.isSome <;> decide)
  have hc3 := nodup_append_of_head_in hc2 h3 (by cases st.session.isSome <;> decide)
  have hc4 := nodup_append_of_head_in hc3 h4 (by cases st.session.isSome <;> decide)
  have hc5 := nodup_append_of_head_in hc4 h5 (by cases st.session.isSome <;> decide)
  rw [hed]; dsimp only [encodeDirHeads]
  simp only [List.map_append, List.append_assoc] at hc5 ⊢
  exact hc5

theorem encodeDir_norm_nodup (W' : PEParams) (st : PqParty)
    (hsig : st.signed.length ≤ 1) (hot : st.oneTime.length ≤ 1)
    (hkot : st.kyberOneTime = []) (hklr : st.kyberLastResort.length ≤ 1) :
    ((encodeDir W' st).map fun f => Arm64.normalizePath f.1).Nodup :=
  (encodeDir_norm_nodup_and_heads W' st hsig hot hkot hklr).1

theorem pqPartyInv_store_bounds {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {p : Participant} {st : PqParty} {d : DirectorySnapshot}
    (h : PqPartyInv interp P r accepted p st d) :
    st.signed.length ≤ 1 ∧ st.oneTime.length ≤ 1 ∧
      st.kyberOneTime = [] ∧ st.kyberLastResort.length ≤ 1 := by
  by_cases hp : p = r.alice
  · obtain ⟨hs, ho, hko, hkl⟩ := h.alice_stores hp; simp [hs, ho, hko, hkl]
  · obtain ⟨hs, hko, ho, ⟨seen, hkl, _, _⟩⟩ := h.bob_stores hp
    refine ⟨by simp [hs], ?_, hko, by simp [hkl]⟩
    rcases ho with ⟨_, ho⟩ | ⟨_, ho | ho⟩ <;> simp [ho]

theorem wfPq_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {p : Participant} {st : PqParty} {d : DirectorySnapshot}
    (h : PqPartyInv interp P r accepted p st d) (hfb : FilesBounded d) :
    PqxdhPartyInSpecDomain P st := by
  obtain ⟨hsig, hot, hkot, hklr⟩ := pqPartyInv_store_bounds h
  have hnd := encodeDir_norm_nodup P st hsig hot hkot hklr
  have hreg := regularFileList_encodeDir P st
  have hcap :=
    LibsignalBinary.Proofs.SignalSession.SessionCap.PqSessionCap.encodeDir_nonBaseKeys_length_le_fileCapBytes
      P st (fun x g hsess => by
        obtain ⟨⟨g₀, hR₀, -, hs₀⟩, -⟩ := h.session_reach x g hsess
        exact ⟨g₀, hR₀, hs₀⟩)
  have hfiles : ∀ f ∈ encodeDir P st, f.2.length < 2 ^ 31 ∧
      ((∀ i, f.1 ≠ baseKeysFile i) → f.2.length ≤ fileCapBytes) := by
    intro f hf
    have hdf : d f.1 = some f.2 := by
      rw [h.dir_eq]; exact filesOf_eq_some_of_mem_nodup hreg hnd hf rfl
    exact ⟨hfb f.1 f.2 hdf, hcap f hf⟩
  have hnd1 : ∀ {α β : Type} (l : List (α × β)), l.length ≤ 1 → (l.map Prod.fst).Nodup := by
    intro α β l hl; cases l with
    | nil => exact List.nodup_nil
    | cons _ tl => cases tl <;> [exact List.nodup_singleton _; simp at hl]
  refine ⟨fun x g hsess => ?_, hfiles, hnd1 _ hsig, hnd1 _ hot, by simp [hkot], hnd1 _ hklr⟩
  obtain ⟨hreach, hgp⟩ := h.session_reach x g hsess
  have hmem : (sessionFile (partyAddress st.party.other), encodeRecordUnderExtras (fun _ => x) g) ∈
      encodeDir P st := by
    unfold encodeDir; simp [hsess]
  exact ⟨hreach, hgp, (hfiles _ hmem).1⟩

theorem encodeRecordX_ne_nil (x : RecordExtras) (g : GhostState HwBytes) :
    encodeRecordUnderExtras (fun _ => x) g ≠ [] := by
  rw [encodeRecordX_eq_encodeRecord_pqSession]
  unfold CryptoVerification.E2E.Record.encodeRecord CryptoVerification.E2E.Record.msgField
    CryptoVerification.E2E.Record.lenField encodeKey
  intro h
  exact encodeVarint_ne_nil _ (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1

theorem oneTimeRecordBytes_ne_nil (C : Crypto) (id : BitVec 32)
    (sk : List.Vector (BitVec 8) 32) :
    oneTimeRecordBytes C id sk ≠ [] := by
  unfold oneTimeRecordBytes CryptoVerification.RecordCodecs.PreKeyRecordStructure.encode
  have h2 : encodeBytesField 2 (some (djbKey (keyPairOf C sk).publicKey.bytes)) ≠ [] := by
    unfold encodeBytesField encodeKey
    intro h
    exact encodeVarint_ne_nil _ (List.append_eq_nil_iff.mp (List.append_eq_nil_iff.mp h).1).1
  intro h
  rcases List.append_eq_nil_iff.mp h with ⟨h12, _⟩
  exact h2 (List.append_eq_nil_iff.mp h12).2

theorem not_mem_encodeDir_head_ne {W' : PEParams} {st : PqParty} {p : String}
    (hhead : ∀ f ∈ encodeDir W' st, (Arm64.normalizePath p).head? ≠ (Arm64.normalizePath f.1).head?) :
    filesOf (encodeDir W' st) p = none :=
  filesOf_eq_none_of_forall_ne (regularFileList_encodeDir W' st) fun f hf heq =>
    hhead f hf (congrArg List.head? heq)

theorem dir_sessionPathOf_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {p : Participant} {st : PqParty} {d : DirectorySnapshot}
    (h : PqPartyInv interp P r accepted p st d) :
    d (sessionPathOf r p) = st.session.map fun (x, g) => encodeRecordUnderExtras (fun _ => x) g := by
  obtain ⟨hsig, hot, hkot, hklr⟩ := pqPartyInv_store_bounds h
  obtain ⟨hnd, hheads⟩ := encodeDir_norm_nodup_and_heads P st hsig hot hkot hklr
  have hreg := regularFileList_encodeDir P st
  rw [h.dir_eq, sessionPathOf_eq_sessionFile, ← h.party_eq]
  cases hsess : st.session with
  | some xg =>
    rcases xg with ⟨x, g⟩
    exact filesOf_eq_some_of_mem_nodup hreg hnd (by unfold encodeDir; simp [hsess]) rfl
  | none =>
    apply not_mem_encodeDir_head_ne; intro f hf heq
    have hsh : (Arm64.normalizePath (sessionFile (partyAddress st.party.other))).head? = some "sessions" := by
      cases st.party <;> decide
    obtain ⟨t, ht, hft⟩ := hheads (Arm64.normalizePath f.1)
      (List.mem_map_of_mem (f := fun x => Arm64.normalizePath x.1) hf)
    rw [hsess] at ht
    rw [hsh, hft] at heq
    injection heq with heq'; subst heq'
    exact absurd ht (by decide)

theorem records_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {t : CliTurn} {p : Participant} {st : PqParty}
    (h : PqPartyInv interp P r accepted p st (t.dirs p)) :
    t.records r p = st.session.map fun (x, g) => encodeRecordUnderExtras (fun _ => x) g := by
  unfold CliTurn.records
  rw [dir_sessionPathOf_of_pqPartyInv h]
  cases st.session with
  | none => rfl
  | some xg => simp [encodeRecordX_ne_nil xg.1 xg.2]

theorem opkUsed_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {t : CliTurn} {stB : PqParty}
    (hne : r.alice ≠ r.bob) (hB : PqPartyInv interp P r accepted r.bob stB (t.dirs r.bob)) :
    (r.withOpk = false → t.opkUsed r = false) ∧
    (r.withOpk = true →
      (t.opkUsed r = false ↔ stB.oneTime = [(r.opkId, some (bytesToVec 32 (secretBytes r 6)))]) ∧
      (t.opkUsed r = true ↔ stB.oneTime = [(r.opkId, none)])) := by
  refine ⟨fun hno => by simp [CliTurn.opkUsed, hno], fun hopk => ?_⟩
  obtain ⟨hsig, hot, hkot, hklr⟩ := pqPartyInv_store_bounds hB
  have hnd := encodeDir_norm_nodup P stB hsig hot hkot hklr
  have hreg := regularFileList_encodeDir P stB
  obtain ⟨_, _, ho, _⟩ := hB.bob_stores hne.symm
  rcases ho with ⟨hno, _⟩ | ⟨_, hot_some | hot_none⟩
  · cases hno.symm.trans hopk
  · have hlookup : t.dirs r.bob (oneTimePreKeyFile r.opkId) =
        some (oneTimeRecordBytes P.C r.opkId (bytesToVec 32 (secretBytes r 6))) := by
      rw [hB.dir_eq]
      exact filesOf_eq_some_of_mem_nodup hreg hnd (by unfold encodeDir; simp [hot_some]) rfl
    have hne_nil := oneTimeRecordBytes_ne_nil P.C r.opkId (bytesToVec 32 (secretBytes r 6))
    have hu : t.opkUsed r = false := by
      simp [CliTurn.opkUsed, hopk, hlookup, hne_nil]
    simp [hu, hot_some]
  · have hlookup : t.dirs r.bob (oneTimePreKeyFile r.opkId) = some [] := by
      rw [hB.dir_eq]
      exact filesOf_eq_some_of_mem_nodup hreg hnd (by unfold encodeDir; simp [hot_none]) rfl
    have hu : t.opkUsed r = true := by simp [CliTurn.opkUsed, hopk, hlookup]
    simp [hu, hot_none]

theorem opkUsed_of_pqBobInv {interp : ExternInterpretation} {P : PEParams} {r : ProtocolSetup}
    {accepted : List HwBytes} {t : CliTurn} {stB : PqParty}
    (hne : r.alice ≠ r.bob) (hB : PqBobInv interp P r accepted t.bobOff stB (t.dirs r.bob)) :
    (r.withOpk = false → t.opkUsed r = false) ∧
    (r.withOpk = true →
      (t.opkUsed r = false ↔ stB.oneTime = [(r.opkId, some (bytesToVec 32 (secretBytes r 6)))]) ∧
      (t.opkUsed r = true ↔ stB.oneTime = [(r.opkId, none)])) := by
  unfold PqBobInv at hB
  cases hbo : t.bobOff
  · rw [hbo] at hB; exact opkUsed_of_pqPartyInv hne hB
  · rw [hbo] at hB
    rcases hB with ⟨d₀, hB₀, hag⟩
    let t₀ : CliTurn := { t with dirs := fun q => if q = r.bob then d₀ else t.dirs q }
    have hopk : t.opkUsed r = t₀.opkUsed r :=
      opkUsed_eq_of_bob_agree fun q hq => by simp [t₀, hag q hq]
    rw [hopk]
    exact opkUsed_of_pqPartyInv hne (by simpa [t₀] using hB₀)

end Symbolic.Swarm.CREF.Cli
