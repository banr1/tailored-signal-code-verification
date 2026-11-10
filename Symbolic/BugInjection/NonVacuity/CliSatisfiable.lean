/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.Proofs.Tests.Refinement.Cli.ExternWitness
import Symbolic.Proofs.Swarm.CREF.Sem
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random

/-!
# Satisfiability of `cliCompFits` for Plausible Witness Setups

Proves `cliCompFits_satisfiable`: every `PQXDHSpqrSetup` satisfying the decidable byte-shape
predicate `Plausible` admits an interpretation, CLI hooks, and `ProtocolSetup` records
(`cliWitnessInterp`, `cliWitnessHooks`, `w.compRecords`) satisfying `cliCompFits`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.X25519 (isLowOrderKey leValue p25519)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement (aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open Symbolic.Proofs.Swarm.WIT.Pure (witnessInterpretation witnessLength)
open Symbolic.Proofs.Tests.Refinement.Cli (cliWitnessInterp cliWitnessHooks
  cliWitnessInterp_contracts cliWitnessHooks_agree)

/-- Default `n`-byte fresh value tagged with leading byte `t` for setup draws not pinned by a
witness (signature nonces and the Kyber seed). -/
def fillFresh (t n : Nat) : HwBytes := BitVec.ofNat 8 t :: List.replicate (n - 1) 0

/-- Canonical 32-byte X25519 public key (`< p25519`, not low-order) for toy witness interpretations. -/
def toyPubKey : HwBytes :=
  hexBytes "abbb904f2c8f86f71332b8059313b1a1cbad7b332d85927b485e5b0e1049c34d"

def toyNonzeroAgreement : HwBytes :=
  1#8 :: List.replicate 31 0

def toyAgreement (point : HwBytes) : HwBytes :=
  if isLowOrderKey (point.map BitVec.toNat) then List.replicate 32 0
  else toyNonzeroAgreement

theorem toyPubKey_length : toyPubKey.length = 32 := by decide
theorem toyPubKey_lt_p25519 : leValue (toyPubKey.map BitVec.toNat) < p25519 := by decide
theorem toyPubKey_not_lowOrder : isLowOrderKey (toyPubKey.map BitVec.toNat) = false := by decide
theorem toyNonzeroAgreement_length : toyNonzeroAgreement.length = 32 := by decide
theorem toyNonzeroAgreement_ne_zero : toyNonzeroAgreement ≠ List.replicate 32 0 := by decide

theorem length_toyAgreement (point : HwBytes) : (toyAgreement point).length = 32 := by
  unfold toyAgreement
  split
  · simp
  · exact toyNonzeroAgreement_length

/-- Decidable byte-length, slice, and torsion-shift conditions on `w` sufficient for `cliCompFits`. -/
def PQXDHSpqrSetup.Plausible (w : PQXDHSpqrSetup) : Prop :=
  w.aliceId.length = 32 ∧ w.bobId.length = 32 ∧ w.spk.length = 32 ∧ w.spkSig.length = 64 ∧
    w.kyberPk.length = 1568 ∧ w.kyberPkSig.length = 64 ∧ w.kyberSec.length = 3169 ∧
    slice w.kyberSec 1537 1568 = w.kyberPk ∧
    [w.aliceId, w.bobId, w.spk, fillFresh 11 64, fillFresh 16 64, fillFresh 17 64].Nodup ∧
    ∀ ab ∈ w.torsionShifts,
      ab.1.length = 32 ∧ ab.2.length = 32 ∧
      isLowOrderKey (ab.1.map BitVec.toNat) = false ∧
      isLowOrderKey (ab.2.map BitVec.toNat) = false ∧
      (w.torsionShifts.find? (fun xy => xy.1 == ab.1)).map Prod.snd = some ab.2

instance (w : PQXDHSpqrSetup) : Decidable w.Plausible := by
  unfold PQXDHSpqrSetup.Plausible; infer_instance

/-- Concrete fresh-byte schedule placing `w.aliceId`, `w.bobId`, and `w.spk` at `t = 0, 5, 10` and
`fillFresh` elsewhere. -/
def PQXDHSpqrSetup.fresh (w : PQXDHSpqrSetup) (t n : Nat) : HwBytes :=
  if t = 0 ∧ n = 32 then w.aliceId else if t = 5 ∧ n = 32 then w.bobId
  else if t = 10 ∧ n = 32 then w.spk else fillFresh t n

theorem fillFresh_ne_11_17 : fillFresh 17 64 ≠ fillFresh 11 64 := by decide

def PQXDHSpqrSetup.compSem (w : PQXDHSpqrSetup) : OpaqueSymbolSemantics where
  init := fun _ _ => []
  chainKey := fun _ _ _ => []
  sendState := fun _ _ => []
  sendKey := fun _ _ => []
  sendMsg := fun _ _ => []
  recvState := fun _ _ => []
  recvKey := fun _ _ => []
  kemPk := fun _ => w.kyberPk
  kemDecap := fun _ _ => []
  vk := fun _ => []
  sign := fun _ n _ => if n = fillFresh 11 64 then w.spkSig else w.kyberPkSig

def PQXDHSpqrSetup.compGhost (w : PQXDHSpqrSetup) : Ghost where
  σ := w.fresh
  addr := fun _ => []

def PQXDHSpqrSetup.compRecords (w : PQXDHSpqrSetup) :
    DY.Libsignal.Composed.Refinement.ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false, regIdA := w.regIdA, regIdB := w.regIdB,
    spkId := w.spkId, kpkId := w.kpkId, opkId := 0, kyberSecB := w.kyberSec, fresh := w.fresh,
    opaqueBytes :=
      DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost }

unseal DY.Bytes in
instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem comp_gamma_randTerm_pos (w : PQXDHSpqrSetup) (i n : Nat) (hn : n ≠ 0) :
    DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost
      (DY.Libsignal.Composed.Refinement.randTerm i n) = w.compGhost.σ i n := by
  unfold DY.Libsignal.Composed.Refinement.gamma
    DY.Libsignal.Composed.Refinement.gamma'
  conv => lhs; unfold DY.Libsignal.Composed.Refinement.randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom w.compGhost) (concretizeAll cliWitnessInterp w.compSem w.compGhost)]
  simp only [concretizeRandom, hn, ite_false]
  rfl

theorem comp_gamma_kemPk (w : PQXDHSpqrSetup) (sk : DY.Bytes) :
    DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost
      (DY.PQKem.kemPk sk) =
      w.compSem.kemPk
        (DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost sk) := by
  unfold DY.Libsignal.Composed.Refinement.gamma
    DY.Libsignal.Composed.Refinement.gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (concretizeAll cliWitnessInterp w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk w.compSem) (concretizeAll cliWitnessInterp w.compSem w.compGhost)]; rfl

theorem comp_gamma_sign (w : PQXDHSpqrSetup) (sk n m : DY.Bytes) :
    DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost
      (DY.Signature.sign sk n m) =
      w.compSem.sign
        (DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost sk)
        (DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost n)
        (DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost m) := by
  unfold DY.Libsignal.Composed.Refinement.gamma
    DY.Libsignal.Composed.Refinement.gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll cliWitnessInterp w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign w.compSem) (concretizeAll cliWitnessInterp w.compSem w.compGhost)]; rfl

theorem compRecords_ne (w : PQXDHSpqrSetup) : w.compRecords.alice ≠ w.compRecords.bob := by
  show ("alice" : String) ≠ "bob"; decide

theorem compRecords_alice (w : PQXDHSpqrSetup) : w.compRecords.alice = "alice" := rfl
theorem compRecords_bob (w : PQXDHSpqrSetup) : w.compRecords.bob = "bob" := rfl
theorem compRecords_withOpk (w : PQXDHSpqrSetup) : w.compRecords.withOpk = false := rfl

def compT4 : DY.ExecTrace :=
  ((DY.Libsignal.Composed.Refinement.setupAct "alice" "bob" false).run DY.Trace.nil).2.val

theorem compRecords_setupTrace (w : PQXDHSpqrSetup) :
    DY.Libsignal.Composed.Refinement.setupTrace w.compRecords = compT4 := by
  unfold DY.Libsignal.Composed.Refinement.setupTrace compT4
  rw [compRecords_alice, compRecords_bob, compRecords_withOpk]

theorem compRecords_randomsAt (w : PQXDHSpqrSetup) :
    DY.Libsignal.Composed.Refinement.setupRandomsAt w.compRecords =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] :=
  Symbolic.Swarm.CREF.b1_setupRandomsAt_eq w.compRecords (compRecords_ne w)

theorem compRecords_public (w : PQXDHSpqrSetup) :
    DY.Libsignal.Composed.Refinement.setupPublic w.compRecords 5 =
      DY.Signature.sign (DY.Libsignal.Composed.Refinement.randTerm 5 32)
        (DY.Libsignal.Composed.Refinement.randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC
          (DY.DiffieHellman.dhPk (DY.Libsignal.Composed.Refinement.randTerm 10 32))) ∧
    DY.Libsignal.Composed.Refinement.setupPublic w.compRecords 6 =
      DY.PQKem.kemPk (DY.Libsignal.Composed.Refinement.randTerm 16 64) ∧
    DY.Libsignal.Composed.Refinement.setupPublic w.compRecords 7 =
      DY.Signature.sign (DY.Libsignal.Composed.Refinement.randTerm 5 32)
        (DY.Libsignal.Composed.Refinement.randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM
          (DY.PQKem.kemPk (DY.Libsignal.Composed.Refinement.randTerm 16 64))) :=
  ⟨Symbolic.Swarm.CREF.b1_setupPublic_5 w.compRecords (compRecords_ne w),
   Symbolic.Swarm.CREF.b1_setupPublic_6 w.compRecords (compRecords_ne w),
   Symbolic.Swarm.CREF.b1_setupPublic_7 w.compRecords (compRecords_ne w)⟩

/-- Every plausible witness setup admits an interpretation, CLI hooks, and `ProtocolSetup` records
satisfying `cliCompFits`. -/
theorem cliCompFits_satisfiable (w : PQXDHSpqrSetup) (h : w.Plausible) :
    ∃ iw r, cliCompFits w iw r := by
  obtain ⟨ha, hb, hs, hss, hk, hks, hsec, hslice, hnd, _⟩ := h
  obtain ⟨h5, h6, h7⟩ := compRecords_public w
  have hR := compRecords_randomsAt w
  have o5 : w.compRecords.opaqueBytes
      (DY.Libsignal.Composed.Refinement.setupPublic w.compRecords 5) = w.spkSig := by
    rw [h5]
    show DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost _ = _
    rw [comp_gamma_sign]
    show (if DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost
        (DY.Libsignal.Composed.Refinement.randTerm 11 64) = fillFresh 11 64
      then _ else _) = _
    rw [comp_gamma_randTerm_pos w 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  have o6 : w.compRecords.opaqueBytes
      (DY.Libsignal.Composed.Refinement.setupPublic w.compRecords 6) = w.kyberPk := by
    rw [h6]
    show DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost _ = _
    rw [comp_gamma_kemPk]; rfl
  have o7 : w.compRecords.opaqueBytes
      (DY.Libsignal.Composed.Refinement.setupPublic w.compRecords 7) =
        w.kyberPkSig := by
    rw [h7]
    show DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost _ = _
    rw [comp_gamma_sign]
    show (if DY.Libsignal.Composed.Refinement.gamma cliWitnessInterp w.compSem w.compGhost
        (DY.Libsignal.Composed.Refinement.randTerm 17 64) = fillFresh 11 64
      then _ else _) = _
    rw [comp_gamma_randTerm_pos w 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]
  have hwf : ProtocolSetupWF w.compRecords := by
    refine ⟨compRecords_ne w, ?_, ?_, ?_, ?_, ?_, hsec, ?_⟩
    · rw [hR]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh, fillFresh, ha, hb, hs]
    · rw [hR]
      simpa [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh] using hnd
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm]; rw [o5]; exact hss
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]; rw [o6]; exact hk
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]; rw [o7]; exact hks
    · show DY.Libsignal.Composed.Refinement.slice w.kyberSec 1537 1568 = _
      dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]
      rw [o6]; exact hslice
  have hs0 : secretBytes w.compRecords 0 = w.aliceId := by
    rw [secretBytes, hR]; simp [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh]
  have hs1 : secretBytes w.compRecords 1 = w.bobId := by
    rw [secretBytes, hR]; simp [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh]
  have hs2 : secretBytes w.compRecords 2 = w.spk := by
    rw [secretBytes, hR]; simp [PQXDHSpqrSetup.compRecords, PQXDHSpqrSetup.fresh]
  have hc := cliWitnessInterp_contracts
  have hlen : ∀ {s : String} {n : Nat}, witnessLength s = some n → ∀ args,
      cliWitnessInterp s args = some (List.replicate n 0#8) := by
    intro s n hw args
    have he : s ≠ aesCbcEncryptSymbol := by rintro rfl; cases hw
    have hd : s ≠ aesCbcDecryptSymbol := by rintro rfl; cases hw
    simp [cliWitnessInterp, he, hd, witnessInterpretation, hw]
  have hkyb : CompKyberCorrectOn cliWitnessInterp w.compRecords w.kyberCts := by
    intro ct _ e ss _ he
    have henc := hlen (s := kyberEncapsSymbol) (n := 1600) (by decide)
      [w.compRecords.opaqueBytes (setupPublic w.compRecords 6), e]
    have hdec := hlen (s := kyberDecapsSymbol) (n := 32) (by decide)
      [w.compRecords.kyberSecB.drop 1, ct]
    simp only [kyberEncapsBytes, DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm,
      henc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    have hss_eq : ss = List.replicate 32 0#8 := by
      rw [← he.2, List.drop_replicate]
    rw [kyberDecapsBytes, hdec, hss_eq]
  exact ⟨(cliWitnessInterp, cliWitnessHooks), w.compRecords,
    ⟨hwf, rfl, rfl, rfl, rfl, rfl, hs0, hs1, hs2, o5, o6, o7, rfl, hc.1, hc.2.1, hkyb⟩,
    hc, cliWitnessHooks_agree⟩

end Symbolic.BugInjection
