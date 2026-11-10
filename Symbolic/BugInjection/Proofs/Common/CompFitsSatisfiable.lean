/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.CompFitsPin
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.Proofs.Swarm.CREF.Sem
public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli
public import Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupTorsionCli
public import Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli

/-!
# Satisfiability of `cliCompFitsPinned`

Proves that `(compI0, compHooks0)` and `compRecordsI0 w` satisfy `cliCompFitsPinned w` for any
plausible witness setup `w` whose torsion shifts are recorded in `compI0`, and instantiates this
for the three composed Cheval26 CLI witnesses.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable

open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws

def bytesToSha512StateLE (bs : HwBytes) : CryptoVerification.E2E.Sha512State :=
  List.Vector.ofFn fun i : Fin 8 =>
    BitVec.ofNat 64 (bytesToNat ((bs.drop (8 * i.val)).take 8))

def compExecMlKem0 : CryptoVerification.LibsignalSpqrV1.MlKem :=
  { Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compMlKem0 with
    keyPair := fun seed => CryptoVerification.E2E.fitVec 2400 (compMlkem768FromSeed seed.toList) }

/-- Concrete `CliHooks` extending `CompI0Laws.compHooks0` with `DefsCompI0`'s recorded SHA-512,
Edwards, scalar, and ML-KEM tables on internal `PqxdhPrims` fields. -/
def compHooks0 : CryptoVerification.SignalSession.CliHooks :=
  { Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compHooks0 with
    Q :=
      { Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compHooks0.Q with
        F512 := fun st blk =>
          bytesToSha512StateLE (compSha512 (CryptoVerification.E2E.sha512StateBytesLE st) blk)
        compress := fun pt => CryptoVerification.E2E.fitVec 32 (compEdwardsCompress pt.toList)
        edNeg := fun pt => CryptoVerification.E2E.fitVec 160 (compEdwardsNeg pt.toList)
        dsmb := fun a pt b =>
          CryptoVerification.E2E.fitVec 160 (compDoubleScalarMul a.toList pt.toList b.toList)
        scalarMod := fun s => CryptoVerification.E2E.fitVec 32 (compScalarModOrder s.toList)
        scalarWide := fun w => CryptoVerification.E2E.fitVec 32 (compScalarModOrderWide w.toList)
        K := compExecMlKem0 } }

theorem compI0_hooksAgree : HooksMatchInterpretation compI0 compHooks0 :=
  Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compI0_hooksMatch

theorem compI0_externContractsHoldCli : ExternContractsHoldCli compI0 :=
  Symbolic.BugInjection.Proofs.Common443.CompI0Laws.compI0_externContractsHoldCli

/-- Combines `compFitsPinned w` with `ExternContractsHoldCli` and `HooksMatchInterpretation` for
CLI ELF refinement witnesses. -/
def cliCompFitsPinned (w : PQXDHSpqrSetup)
    (iw : ExternInterpretation × CryptoVerification.SignalSession.CliHooks)
    (r : ProtocolSetup) : Prop :=
  compFitsPinned w iw.1 r ∧
    ExternContractsHoldCli iw.1 ∧
    HooksMatchInterpretation iw.1 iw.2

/-- Canonical `ProtocolSetup` built from `w` under `compI0`. -/
def compRecordsI0 (w : PQXDHSpqrSetup) : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false, regIdA := w.regIdA, regIdB := w.regIdB,
    spkId := w.spkId, kpkId := w.kpkId, opkId := 0, kyberSecB := w.kyberSec, fresh := w.fresh,
    opaqueBytes := gamma compI0 w.compSem w.compGhost }

theorem compI0_gamma_randTerm_pos (w : PQXDHSpqrSetup) (i n : Nat) (hn : n ≠ 0) :
    gamma compI0 w.compSem w.compGhost (randTerm i n) = w.compGhost.σ i n := by
  unfold gamma gamma'
  conv => lhs; unfold randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom w.compGhost) (concretizeAll compI0 w.compSem w.compGhost)]
  simp only [concretizeRandom, hn, ite_false]
  rfl

theorem compI0_gamma_kemPk (w : PQXDHSpqrSetup) (sk : DY.Bytes) :
    gamma compI0 w.compSem w.compGhost (DY.PQKem.kemPk sk) =
      w.compSem.kemPk (gamma compI0 w.compSem w.compGhost sk) := by
  unfold gamma gamma'
  show ((({sk} : DY.PQKem.Pk.SubF DY.Bytes).pack).rec
    (concretizeAll compI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeKemPk w.compSem) (concretizeAll compI0 w.compSem w.compGhost)]
  rfl

theorem compI0_gamma_sign (w : PQXDHSpqrSetup) (sk n m : DY.Bytes) :
    gamma compI0 w.compSem w.compGhost (DY.Signature.sign sk n m) =
      w.compSem.sign
        (gamma compI0 w.compSem w.compGhost sk)
        (gamma compI0 w.compSem w.compGhost n)
        (gamma compI0 w.compSem w.compGhost m) := by
  unfold gamma gamma'
  show ((({sk, nonce := n, msg := m} : DY.Signature.Sign.SubF DY.Bytes).pack).rec
    (concretizeAll compI0 w.compSem w.compGhost)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSign w.compSem) (concretizeAll compI0 w.compSem w.compGhost)]
  rfl

theorem compRecordsI0_ne (w : PQXDHSpqrSetup) :
    (compRecordsI0 w).alice ≠ (compRecordsI0 w).bob := by
  show ("alice" : String) ≠ "bob"; decide

theorem compRecordsI0_randomsAt (w : PQXDHSpqrSetup) :
    setupRandomsAt (compRecordsI0 w) =
      [(0, 32), (5, 32), (10, 32), (11, 64), (16, 64), (17, 64)] := by
  rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq (compRecordsI0 w) (compRecordsI0_ne w)]
  rfl

theorem compRecordsI0_public (w : PQXDHSpqrSetup) :
    setupPublic (compRecordsI0 w) 5 =
      DY.Signature.sign (randTerm 5 32) (randTerm 11 64)
        (DY.Libsignal.PQXDH.encodeEC (DY.DiffieHellman.dhPk (randTerm 10 32))) ∧
    setupPublic (compRecordsI0 w) 6 =
      DY.PQKem.kemPk (randTerm 16 64) ∧
    setupPublic (compRecordsI0 w) 7 =
      DY.Signature.sign (randTerm 5 32) (randTerm 17 64)
        (DY.Libsignal.PQXDH.encodeKEM (DY.PQKem.kemPk (randTerm 16 64))) :=
  ⟨Symbolic.Swarm.CREF.b1_setupPublic_5 (compRecordsI0 w) (compRecordsI0_ne w),
   Symbolic.Swarm.CREF.b1_setupPublic_6 (compRecordsI0 w) (compRecordsI0_ne w),
   Symbolic.Swarm.CREF.b1_setupPublic_7 (compRecordsI0 w) (compRecordsI0_ne w)⟩

theorem cliCompFitsPinned_satisfiable_of_plausible (w : PQXDHSpqrSetup)
    (h : w.Plausible) (htor : TorsionShiftsRecorded compI0 w.torsionShifts) :
    ∃ iw r, cliCompFitsPinned w iw r := by
  obtain ⟨ha, hb, hs, hss, hk, hks, hsec, hslice, hnd, _⟩ := h
  obtain ⟨h5, h6, h7⟩ := compRecordsI0_public w
  have hR := compRecordsI0_randomsAt w
  have o5 : (compRecordsI0 w).opaqueBytes (setupPublic (compRecordsI0 w) 5) = w.spkSig := by
    rw [h5]
    show gamma compI0 w.compSem w.compGhost _ = _
    rw [compI0_gamma_sign]
    show (if gamma compI0 w.compSem w.compGhost (randTerm 11 64) = fillFresh 11 64
      then _ else _) = _
    rw [compI0_gamma_randTerm_pos w 11 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh]
  have o6 : (compRecordsI0 w).opaqueBytes (setupPublic (compRecordsI0 w) 6) = w.kyberPk := by
    rw [h6]
    show gamma compI0 w.compSem w.compGhost _ = _
    rw [compI0_gamma_kemPk]; rfl
  have o7 : (compRecordsI0 w).opaqueBytes (setupPublic (compRecordsI0 w) 7) = w.kyberPkSig := by
    rw [h7]
    show gamma compI0 w.compSem w.compGhost _ = _
    rw [compI0_gamma_sign]
    show (if gamma compI0 w.compSem w.compGhost (randTerm 17 64) = fillFresh 11 64
      then _ else _) = _
    rw [compI0_gamma_randTerm_pos w 17 64 (by decide)]
    simp [PQXDHSpqrSetup.compGhost, PQXDHSpqrSetup.fresh, fillFresh_ne_11_17]
  have hwf : ProtocolSetupWF (compRecordsI0 w) := by
    refine ⟨compRecordsI0_ne w, ?_, ?_, ?_, ?_, ?_, hsec, ?_⟩
    · rw [hR]
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [compRecordsI0, PQXDHSpqrSetup.fresh, fillFresh, ha, hb, hs]
    · rw [hR]
      simpa [compRecordsI0, PQXDHSpqrSetup.fresh] using hnd
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.spkSigTerm]; rw [o5]; exact hss
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]; rw [o6]; exact hk
    · dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkSigTerm]; rw [o7]; exact hks
    · show slice w.kyberSec 1537 1568 = _
      dsimp only [DY.Libsignal.Composed.Refinement.ProtocolSetup.pqpkPubTerm]
      rw [o6]; exact hslice
  have hs0 : secretBytes (compRecordsI0 w) 0 = w.aliceId := by
    rw [secretBytes, hR]; simp [compRecordsI0, PQXDHSpqrSetup.fresh]
  have hs1 : secretBytes (compRecordsI0 w) 1 = w.bobId := by
    rw [secretBytes, hR]; simp [compRecordsI0, PQXDHSpqrSetup.fresh]
  have hs2 : secretBytes (compRecordsI0 w) 2 = w.spk := by
    rw [secretBytes, hR]; simp [compRecordsI0, PQXDHSpqrSetup.fresh]
  have hs3 : secretBytes (compRecordsI0 w) 3 = fillFresh 11 64 := by
    rw [secretBytes, hR]; simp [compRecordsI0, PQXDHSpqrSetup.fresh]
  have hs4 : secretBytes (compRecordsI0 w) 4 = fillFresh 16 64 := by
    rw [secretBytes, hR]; simp [compRecordsI0, PQXDHSpqrSetup.fresh]
  have hs5 : secretBytes (compRecordsI0 w) 5 = fillFresh 17 64 := by
    rw [secretBytes, hR]; simp [compRecordsI0, PQXDHSpqrSetup.fresh]
  exact ⟨(compI0, compHooks0), compRecordsI0 w,
    ⟨⟨hwf, rfl, rfl, rfl, rfl, rfl, hs0, hs1, hs2, o5, o6, o7, rfl,
      compI0_cryptoEquationsHold, compI0_pubCanonical,
      compI0_kyberCorrectOn (compRecordsI0 w) w.kyberCts⟩,
     rfl, ⟨hs3, hs4, hs5⟩, ⟨rfl, rfl⟩,
     compI0_torsionShiftsRejected, htor⟩,
    compI0_externContractsHoldCli, compI0_hooksAgree⟩

theorem cliCompFitsPinned_satisfiable_hb :
    ∃ iw r, cliCompFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup iw r :=
  cliCompFitsPinned_satisfiable_of_plausible
    Witnesses.Cheval26SmallSubgroupHighBitCli.setup
    (by decide +kernel)
    (fun _ h => nomatch h)

theorem cliCompFitsPinned_satisfiable_tor :
    ∃ iw r, cliCompFitsPinned Witnesses.Cheval26SmallSubgroupTorsionCli.setup iw r := by
  refine cliCompFitsPinned_satisfiable_of_plausible
    Witnesses.Cheval26SmallSubgroupTorsionCli.setup
    (by decide +kernel)
    (fun ab hab => ?_)
  simp only [Witnesses.Cheval26SmallSubgroupTorsionCli.setup, List.mem_singleton] at hab
  subst hab
  exact ⟨1, torsionShift_compI0_ekAPub_one⟩

theorem cliCompFitsPinned_satisfiable_ws1 :
    ∃ iw r, cliCompFitsPinned Witnesses.Cheval26WeakStateIdx1Cli.setup iw r :=
  cliCompFitsPinned_satisfiable_of_plausible
    Witnesses.Cheval26WeakStateIdx1Cli.setup
    (by decide +kernel)
    (fun _ h => nomatch h)

end Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
