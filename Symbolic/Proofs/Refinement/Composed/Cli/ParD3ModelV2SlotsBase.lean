/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Refinement.Composed.Cli.ParD3RpkSlot
public import Symbolic.Proofs.Swarm.CREF.Cli.DirStepAux
import Symbolic.Proofs.Refinement.Composed.Cli.Transfer
import Symbolic.Proofs.Swarm.CREF.Cli.ModelRel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateRecord
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateRecordAux
import Symbolic.Proofs.Swarm.CREF.Cli.World.TopPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.CallCountPure
import Symbolic.Proofs.SpecLemmas.Refinement.Composed.ModelTraces
import Symbolic.Proofs.Swarm.CREF.Xpl.InvCommon
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlots
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvWhisperSlot
import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Cli.HooksBridge
import Symbolic.Proofs.Swarm.CREF.Cli.DirStepBridge
import Symbolic.Proofs.Swarm.CREF.Cli.TopSlotsSend
import Symbolic.Proofs.Swarm.CREF.Cli.World.InitModelPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.InitPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.LeakPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.TurnPure
import Symbolic.Proofs.Swarm.CREF.Cli.World.XplTransferPure
import Symbolic.Proofs.Swarm.CREF.Initiate.EntryPureB
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Flat-Bundle Regularity, Scrubbing, and Typed-Bundle Lemmas

Proves that flat bundle file lists satisfy `RegularFileList` and `IsScrubbedPath`, and that
`parseBundleFiles` produces `BundleTyped` bundles.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace DY.Libsignal.Composed.Refinement.Cli.ParD3

cref_open
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent StateAndMessage)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF
open Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli

theorem regularFileList_of_bundleFilesFlat {files : List (String × HwBytes)}
    (hflat : BundleFilesFlat files) : RegularFileList files := by
  intro f hf
  obtain ⟨⟨name, hp⟩, _⟩ := hflat f hf
  exact regularFile_two hp (by decide) f (List.mem_singleton.mpr rfl)

theorem isScrubbedPath_of_bundleFilesFlat {files : List (String × HwBytes)}
    (hflat : BundleFilesFlat files) : ∀ f ∈ files, IsScrubbedPath f.1 = true := by
  intro f hf
  obtain ⟨⟨name, hp⟩, _⟩ := hflat f hf
  unfold IsScrubbedPath
  simp [hp]

private theorem parseEcKey_inv {bs out : HwBytes} (h : parseEcKey bs = some out) :
    out.length = 33 ∧ out.head? = some 5#8 := by
  cases bs with
  | nil => simp [parseEcKey, ecKeyParses] at h
  | cons t rest =>
    simp only [parseEcKey, ecKeyParses, List.head?_cons, Option.some_beq_some, beq_iff_eq,
      List.length_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    split_ifs at h with ht
    injection h with hout
    subst hout
    rcases ht with ⟨rfl, hlen⟩
    exact ⟨by simp [List.take_succ_cons]; omega, rfl⟩

private theorem parseKyberKey_inv {bs out : HwBytes} (h : parseKyberKey bs = some out) :
    out.length = 1569 ∧ out.head? = some 8#8 := by
  cases bs with
  | nil => simp [parseKyberKey] at h
  | cons t rest =>
    dsimp only [parseKyberKey] at h
    split_ifs at h with ht
    injection h with hout
    subst hout
    rcases ht with ⟨rfl, hlen⟩
    exact ⟨by simp [hlen], rfl⟩

private theorem bundleSplitSigned_sig_len {bs : HwBytes} {id : BitVec 32} {k sig : HwBytes}
    (h : bundleSplitSigned bs = some (id, k, sig)) : sig.length = 64 := by
  unfold bundleSplitSigned at h
  cases hbs : bundleSplitId bs with
  | none => rw [hbs] at h; cases h
  | some p =>
    rcases p with ⟨id₀, rest⟩
    rw [hbs] at h
    dsimp only at h
    split_ifs at h with hlen
    injection h with hp
    rcases Prod.mk.inj hp with ⟨_, hks⟩
    rcases Prod.mk.inj hks with ⟨_, hsig⟩
    subst hsig
    simp [List.length_drop]; omega

theorem bundleTyped_of_parseBundleFiles {d : DirectorySnapshot} {pb : PublicBundle}
    (h : parseBundleFiles d = some pb) : BundleTyped pb := by
  unfold parseBundleFiles at h
  let file := fun name => (d (bundleDir ++ "/" ++ name)).getD []
  change (do
    let identityKey ← parseEcKey (file "identity-key")
    let registrationId ← bundleU32 (file "registration-id")
    let (signedId, spk, signedSig) ← bundleSplitSigned (file "signed-pre-key")
    let (kyberId, kpk, kyberSig) ← bundleSplitSigned (file "kyber-pre-key")
    let oneTime ← (match file "one-time-pre-key" with
      | [] => some none
      | opk => do
        let (id, key) ← bundleSplitId opk
        let key ← parseEcKey key
        some (some (id, key)) : Option (Option (BitVec 32 × HwBytes)))
    let signedKey ← parseEcKey spk
    let kyberKey ← parseKyberKey kpk
    some { identityKey, registrationId, signedId, signedKey, signedSig, kyberId, kyberKey, kyberSig,
           oneTime }) = some pb at h
  generalize hot_def : (match file "one-time-pre-key" with
    | [] => some none
    | opk => do
      let (id, key) ← bundleSplitId opk
      let key ← parseEcKey key
      some (some (id, key)) : Option (Option (BitVec 32 × HwBytes))) = otOpt at h
  dsimp only [Bind.bind, Option.bind] at h
  cases hik : parseEcKey (file "identity-key") with
  | none => simp [hik] at h
  | some identityKey =>
    rw [hik] at h; dsimp only at h
    cases hreg : bundleU32 (file "registration-id") with
    | none => simp [hreg] at h
    | some registrationId =>
      rw [hreg] at h; dsimp only at h
      cases hss : bundleSplitSigned (file "signed-pre-key") with
      | none => simp [hss] at h
      | some sp =>
        rcases sp with ⟨signedId, spk, signedSig⟩
        rw [hss] at h; dsimp only at h
        cases hks : bundleSplitSigned (file "kyber-pre-key") with
        | none => simp [hks] at h
        | some kp =>
          rcases kp with ⟨kyberId, kpk, kyberSig⟩
          rw [hks] at h; dsimp only at h
          cases otOpt with
          | none => simp at h
          | some oneTime =>
            dsimp only at h
            cases hsk : parseEcKey spk with
            | none => simp [hsk] at h
            | some signedKey =>
              rw [hsk] at h; dsimp only at h
              cases hkk : parseKyberKey kpk with
              | none => simp [hkk] at h
              | some kyberKey =>
                rw [hkk] at h; dsimp only at h
                injection h with hpb_eq
                subst hpb_eq
                obtain ⟨hik1, hik2⟩ := parseEcKey_inv hik
                obtain ⟨hsk1, hsk2⟩ := parseEcKey_inv hsk
                obtain ⟨hkk1, hkk2⟩ := parseKyberKey_inv hkk
                refine ⟨hik1, hik2, hsk1, hsk2, bundleSplitSigned_sig_len hss,
                  hkk1, hkk2, bundleSplitSigned_sig_len hks, fun id1 key1 hs => ?_⟩
                subst hs
                cases hopk_f : file "one-time-pre-key" with
                | nil => rw [hopk_f] at hot_def; cases hot_def
                | cons b0 bs =>
                  rw [hopk_f] at hot_def
                  dsimp only [Bind.bind, Option.bind] at hot_def
                  cases hsid : bundleSplitId (b0 :: bs) with
                  | none => rw [hsid] at hot_def; cases hot_def
                  | some ik0 =>
                    rw [hsid] at hot_def; dsimp only at hot_def
                    cases hec : parseEcKey ik0.2 with
                    | none => rw [hec] at hot_def; cases hot_def
                    | some key =>
                      rw [hec] at hot_def; dsimp only at hot_def
                      rcases Prod.mk.inj (Option.some.inj (Option.some.inj hot_def)) with ⟨_, rfl⟩
                      exact parseEcKey_inv hec

/--
info: 'DY.Libsignal.Composed.Refinement.Cli.ParD3.slot_rpk_d3_pqModelRel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms slot_rpk_d3_pqModelRel

end DY.Libsignal.Composed.Refinement.Cli.ParD3
