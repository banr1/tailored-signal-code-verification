/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FsAtomicBundles
import Computational.Proofs.ReductionDsl.FSAEAD.HybridRed
import Computational.Proofs.GameHop.StateSim

/-!
# Evaluation and `CoinSimEquiv` Bridges for `fsCostedRedsInst`

Proves exact evaluation equality for `pubRed` and `CoinSimEquiv` soundness with query-count
preservation at `clampedProtoSignalCodec` for `prgRedZero`, `multiRed`, `slotSaltRed`, `lSaltRed`,
`slotWireRed`, and `lWireRed`.
-/

@[expose] public section

set_option autoImplicit false

open ReductionDsl (Sig Ty Var Env Expr Comp Samplers Ops Iface GameCodec CostedReduction
  TwoStageCostedReduction UniformSamplerTag unifSamplers unifSamplers0 isGameQuery AtomicSort
  atomicSig AtomicBaseUnif atomicBaseSamplers atomicFsOps fitBytesN salt32V salt32OfV
  wireSignalHdrV wireSignalHdrOfV lpubV lpubOfV wireSaltCtV wireSaltCtOfV lctV lctOfV
  fig8PubAdV fig8PubAdOfV slotAdV slotAdOfV fsSendStV fsSendStOfV fsRecvStV fsRecvStOfV
  fsRrEnc fsRrDec OTCCATag FSAEADTag coinOnlyBaseIface saltPrfTargetIface wireOtccaTargetIface
  slotOtccaTargetIface fsaeadPubTargetIface fsaeadPubCodec fsaeadRatchetCodec slotOtccaCodec)

namespace Computational.Proofs.ReductionDsl.FsAtomicSoundness

open OracleSpec OracleComp
open _root_.CryptoGames (Party AEADScheme MACScheme WireAEAD)
open _root_.CryptoGames.HKDF (DerivedMessageKeys)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.Ratchet.LibsignalInst (Salt32 LibsignalCiphertextWithSalt32 LibsignalMsgPublicPart
  lIds lHeader lWire lAeadK lPubOf lChainPRG lAeadR lIdeal lSaltRed lWireRed slotSaltRed slotWireRed)
open _root_.CryptoGames.SM.Construction (Header)
open _root_.CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey SignalHeader
  SignalMessageProtoCodec maxForwardJumps)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState ReceiveResult)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSession (LCt FsAdv evalTwoStage1 pubToAD pubToADCosted
  multiSlotAdv multiSlotAdvCosted)
open Computational.Proofs.ReductionDsl.MacroLift (mapTy toVal guardTwoStageRed guardTwoStageRed_pos)
open Computational.Proofs.ReductionDsl.FsAtomicMacros (CoinSimEquiv compilePureRed
  compilePureRed_eval_eq compilePureRed_coinSimEquiv compilePureTwoStageRed
  compilePureTwoStageRed_coinSimEquiv CostedReduction.eval_coinSimEquiv_congr
  salt32OfV_salt32V salt32V_salt32OfV wireSignalHdrOfV_wireSignalHdrV wireSignalHdrV_wireSignalHdrOfV
  lpubOfV_lpubV lpubV_lpubOfV wireSaltCtOfV_wireSaltCtV wireSaltCtV_wireSaltCtOfV
  lctOfV_lctV lctV_lctOfV fig8PubAdOfV_fig8PubAdV fig8PubAdV_fig8PubAdOfV
  slotAdOfV_slotAdV slotAdV_slotAdOfV fsSendStOfV_fsSendStV fsSendStV_fsSendStOfV
  fsRecvStOfV_fsRecvStV fsRecvStV_fsRecvStOfV fsRrDec_fsRrEnc fitBytesN_toList)
open Computational.Proofs.ReductionDsl.FsAtomicOps (env_get_zero env_get_succ clampedProtoSignalCodec
  lPubOfExpr_eval chainGenExpr_eval lIdsExpr_eval lHeaderExpr_eval eqWireSignalHdrExpr_eval
  fitPlainExpr_eval eqPlainExpr_eval eqSaltExpr_eval saltOfSlotAdExpr_eval
  eqFig8PubAdExpr_eval eqSlotAdExpr_eval eqWireSaltCtExpr_eval
  aeadKEncExpr_eval aeadKDecExpr_eval aeadREncExpr_eval aeadRDecExpr_eval
  sampleMsgKeyComp_coinSimEquiv sampleIdealComp_coinSimEquiv)
open Computational.Proofs.ReductionDsl.FsAtomicBundles

section PubBridge

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

omit [DecidableEq Pt] in
theorem fsPubRedAtomic_eval_eq (A : FsAdv Pt ℓ) :
    (fsPubRedAtomic C ℓ encT).eval (fun _ => A) () = pubToAD protoSignalCodec A := by
  have hRed := compilePureRed_eval_eq (fsaeadPubCodec ℓ Pt)
    (pubMacroBundle (Pt := Pt) C ℓ encT)
    (CryptoGames.FSAEAD.Costed.pubRedProg
      (SS := RatchetSenderState (BitVec 256))
      (RS := RatchetReceiverState (BitVec 256) (BitVec 256))
      (AD := Header Pt) (M := Plain ℓ)
      (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2) 1)
    rfl rfl
    (fun _ => rfl)
    (fun o x => by
      cases o; rcases x with ⟨i, c⟩
      dsimp only [pubMacroBundle, pubBaseTy, pubToDen, mapTy, toVal,
        CryptoGames.FSAEAD.Costed.fsOps, lctV, id]
      rw [lPubOfExpr_eval]
      simp only [Expr.eval, env_get_zero, wireSaltCtOfV_wireSaltCtV])
    (fun s => nomatch s)
    (fun g x => by
      cases g
      · dsimp only [pubMacroBundle, pubBaseTy, pubToDen, mapTy, toVal, fsaeadPubTargetIface,
          CryptoGames.FSAEAD.Costed.fsaeadIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote, Comp.eval, Expr.eval, fig8PubAdOfV, id] at x ⊢
        rcases x with ⟨⟨h, p⟩, m⟩
        simp only [env_get_zero, Functor.map_map]
        rw [lpubOfV_lpubV]
      · dsimp only [pubMacroBundle, pubBaseTy, pubToDen, mapTy, toVal, fsaeadPubTargetIface,
          CryptoGames.FSAEAD.Costed.fsaeadIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote, Comp.eval, Expr.eval, fig8PubAdOfV, id] at x ⊢
        rcases x with ⟨⟨h, p⟩, m0, m1⟩
        simp only [env_get_zero, Functor.map_map]
        rw [lpubOfV_lpubV]
      · dsimp only [pubMacroBundle, pubBaseTy, pubToDen, mapTy, toVal, fsaeadPubTargetIface,
          CryptoGames.FSAEAD.Costed.fsaeadIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote, Comp.eval, Expr.eval, id] at x ⊢
        cases x
        simp only [Functor.map_map]
      · dsimp only [pubMacroBundle, pubBaseTy, pubToDen, mapTy, toVal, fsaeadPubTargetIface,
          CryptoGames.FSAEAD.Costed.fsaeadIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote, Comp.eval, Expr.eval, id] at x ⊢
        cases x
        simp only [Functor.map_map]
      · dsimp only [pubMacroBundle, pubBaseTy, pubToDen, mapTy, toVal, fsaeadPubTargetIface,
          CryptoGames.FSAEAD.Costed.fsaeadIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, CryptoGames.FSAEAD.Costed.rrTy, Ty.denote,
          Comp.eval, Expr.eval, fig8PubAdOfV, id] at x ⊢
        rcases x with ⟨⟨h, p⟩, c⟩
        simp only [env_get_zero, Functor.map_map]
        rw [lpubOfV_lpubV, lctOfV_lctV]
        congr 1; funext r
        cases r with
        | none => rfl
        | some rr => cases rr with | rejected => rfl | accepted st optM => cases optM <;> rfl
      · dsimp only [pubMacroBundle, pubBaseTy, pubToDen, mapTy, toVal, fsaeadPubTargetIface,
          CryptoGames.FSAEAD.Costed.fsaeadIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, CryptoGames.FSAEAD.Costed.rrTy, Ty.denote,
          Comp.eval, Expr.eval, fig8PubAdOfV, id] at x ⊢
        rcases x with ⟨⟨h, p⟩, c⟩
        simp only [env_get_zero, Functor.map_map]
        rw [lpubOfV_lpubV, lctOfV_lctV]
        congr 1; funext r
        cases r with
        | none => rfl
        | some rr => cases rr with | rejected => rfl | accepted st optM => cases optM <;> rfl)
    (fun t => by
      rcases t with (((((⟨h, p, m⟩ | ⟨h, ⟨p0, m0⟩, ⟨p1, m1⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨h, c⟩) | ⟨h, c⟩) <;> rfl)
    (fun t r₁ => by
      dsimp only [pubMacroBundle, fsaeadPubCodec, CryptoGames.FSAEAD.Costed.pubCodec,
        CryptoGames.FSAEAD.Costed.pubR, CryptoGames.FSAEAD.Costed.bt,
        CryptoGames.FSAEAD.Costed.rrTy, pubBaseTy, mapTy, toVal, pubToDen]
      rcases t with (((((⟨h, p, m⟩ | ⟨h, ⟨p0, m0⟩, ⟨p1, m1⟩⟩) | ⟨⟩) | ⟨⟩) | ⟨h, c⟩) | ⟨h, c⟩) <;>
        rcases r₁ with (r | (r | (r | r))) <;> try rfl
      · cases r <;> simp [lctOfV_lctV]
      · cases r <;> simp [lctOfV_lctV]
      · cases r <;> simp [fsSendStOfV_fsSendStV]
      · cases r <;> simp [fsSendStOfV_fsSendStV, fsRecvStOfV_fsRecvStV]
      · rcases r with _ | (⟨⟩ | ⟨st, _ | ⟨pv, m⟩⟩) <;>
          simp [CryptoGames.FSAEAD.Costed.rrDec, fsRrDec, lpubOfV_lpubV]
      · rcases r with _ | (⟨⟩ | ⟨st, _ | ⟨pv, m⟩⟩) <;>
          simp [CryptoGames.FSAEAD.Costed.rrDec, fsRrDec, lpubOfV_lpubV])
    (fun _ => A) ()
  exact hRed.trans (CryptoGames.FSAEAD.Costed.pubRedProg_eval
    (fun c : ℕ × LCt => lPubOf protoSignalCodec c.2) 1 A)

theorem pubToADCosted_inst_eq (qR : ℕ) (hℓ : ℓ < 10 ^ 6) (A : FsAdv Pt ℓ) :
    pubToADCosted (fsCostedRedsInst C codec ℓ encT idOf qR) A =
      pubToAD protoSignalCodec A := by
  unfold pubToADCosted fsCostedRedsInst
  simp only [hℓ, ↓reduceIte]
  exact fsPubRedAtomic_eval_eq C ℓ encT A

end PubBridge

section HybBridges

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

omit [DecidableEq Pt] in
lemma isQueryBoundP_pubToAD {A : FsAdv Pt ℓ} {qR : ℕ}
    (hA : CryptoGames.FSAEAD.MakesAtMostQueries A qR) :
    (pubToAD clampedProtoSignalCodec A).IsQueryBoundP
      (isGameQuery (G := CryptoGames.FSAEAD.spec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) (ℕ × LCt))) qR := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := CryptoGames.FSAEAD.spec
        (RatchetSenderState (BitVec 256))
        (RatchetReceiverState (BitVec 256) (BitVec 256))
        (Header Pt) (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LCt))) qR :=
    Computational.Proofs.GameHop.StateSim.isQueryBoundP_congr_pred
      (fun x => by cases x <;> simp [isGameQuery]) hA
  have hq := CryptoGames.FSAEAD.Costed.pubRedProg_queries
    (fun c : ℕ × LCt => lPubOf clampedProtoSignalCodec c.2) 1 A qR hA'
  rwa [CryptoGames.FSAEAD.Costed.pubRedProg_eval] at hq

private lemma hybOpMacro_eval (hinj : Function.Injective encT) (o) (x) :
    (hybOpMacro (Pt := Pt) C ℓ encT idOf o).eval
      (.cons (toVal hybBaseTy hybToDen _ x) .nil) =
    toVal hybBaseTy hybToDen _
      ((Ops.sum
        (CryptoGames.PRG.Costed.prgOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.prod .nat (.base .ss)) (.prod (.base .ss) (.base .rs))
          (fun pw => (lChainPRG C.F pw.1).gen pw.2) 1)
        (CryptoGames.OTCCA.Costed.otccaOps
          (S := CryptoGames.FSAEAD.Costed.fsSig (BitVec 256) (BitVec 256)
            (Header Pt × LibsignalMsgPublicPart) Unit (Plain ℓ) LCt)
          (.base .rs) (.prod .nat (.base .ad)) (.base .ad) (.base .msg) (.base .ct)
          (lAeadR C clampedProtoSignalCodec ℓ encT idOf) 1 .unit (fun _ => ()))).eval o x) := by
  rcases o with ⟨⟩ | (_ | _ | _ | _ | _ | _ | _)
  · rcases x with ⟨p, ck⟩
    dsimp only [hybOpMacro, hybBaseTy, hybToDen, mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.PRG.Costed.prgOps, CryptoGames.FSAEAD.Costed.bt]
    exact chainGenExpr_eval ℓ Pt C encT (.snd (.var .zero))
      (.cons (t := .prod .nat (ReductionDsl.BV256 (ℓ := ℓ) (Pt := Pt))) (p, ck) .nil) p
  · rcases x with ⟨seed, ⟨i, a⟩, m⟩
    dsimp only [hybOpMacro, hybBaseTy, hybToDen, mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt, id]
    rw [aeadREncExpr_eval]
    simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
  · rcases x with ⟨seed, ⟨i, a⟩, e⟩
    dsimp only [hybOpMacro, hybBaseTy, hybToDen, mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt, id]
    rw [aeadRDecExpr_eval]
    have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    simp only [hsl, wireSaltCtOfV_wireSaltCtV]
    cases (lAeadR C clampedProtoSignalCodec ℓ encT idOf).dec seed (i, a) e <;> rfl
  · rfl
  · rcases x with ⟨a₁, a₂⟩
    dsimp only [hybOpMacro, hybBaseTy, hybToDen, mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt]
    rw [eqFig8PubAdExpr_eval ℓ Pt C encT hinj]
    simp only [Expr.eval, env_get_zero, fig8PubAdOfV_fig8PubAdV]
    by_cases h : a₁ = a₂ <;> simp [h]
  · rcases x with ⟨m₁, m₂⟩
    dsimp only [hybOpMacro, hybBaseTy, hybToDen, mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt]
    rw [eqPlainExpr_eval]
    simp only [Expr.eval, env_get_zero]
    by_cases h : m₁ = m₂ <;> simp [h]
  · rcases x with ⟨c₁, c₂⟩
    dsimp only [hybOpMacro, hybBaseTy, hybToDen, mapTy, toVal, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.FSAEAD.Costed.bt]
    rw [eqWireSaltCtExpr_eval]
    simp only [Expr.eval, env_get_zero, wireSaltCtOfV_wireSaltCtV]
    by_cases h : c₁ = c₂ <;> simp [h]
  · rcases x with ⟨s₁, s₂⟩; rfl

omit [DecidableEq Pt] in
private lemma hybRdec_eq (t) (r₁) :
    (fsaeadRatchetCodec ℓ Pt).rdec t (toVal hybBaseTy hybToDen _ r₁) =
      (CryptoGames.FSAEAD.Costed.ratchetCodec
        (CK := BitVec 256) (MK := BitVec 256)
        (AD := Header Pt × LibsignalMsgPublicPart) (M := Plain ℓ) (C := LCt)).rdec t r₁ := by
  dsimp only [fsaeadRatchetCodec, CryptoGames.FSAEAD.Costed.ratchetCodec,
    CryptoGames.FSAEAD.Costed.ratchetR, CryptoGames.FSAEAD.Costed.rssTy,
    CryptoGames.FSAEAD.Costed.rrsTy, CryptoGames.FSAEAD.Costed.rrTy,
    CryptoGames.FSAEAD.Costed.bt, hybBaseTy, mapTy, toVal, hybToDen]
  rcases t with (((((⟨a, m⟩ | ⟨a, m0, m1⟩) | ⟨⟩) | ⟨⟩) | ⟨a, c⟩) | ⟨a, c⟩) <;>
    rcases r₁ with (r | (r | (r | r))) <;> try rfl
  · rcases r with _ | ⟨i, c⟩ <;> simp [lctOfV, wireSaltCtOfV_wireSaltCtV]
  · rcases r with _ | ⟨i, c⟩ <;> simp [lctOfV, wireSaltCtOfV_wireSaltCtV]
  · rcases r with _ | ⟨ck, idx⟩ <;> simp [CryptoGames.FSAEAD.Costed.rssDec, fsSendStOfV]
  · rcases r with _ | ⟨⟨ckA, idxA⟩, ⟨ckB, idxB, skB⟩⟩
    · rfl
    · simp [CryptoGames.FSAEAD.Costed.rssDec, CryptoGames.FSAEAD.Costed.rrsDec,
        fsSendStOfV, fsRecvStOfV]
  · rcases r with _ | (⟨⟩ | ⟨st, _ | m⟩) <;>
      simp [CryptoGames.FSAEAD.Costed.rrDecM, fsRrDec]
  · rcases r with _ | (⟨⟩ | ⟨st, _ | m⟩) <;>
      simp [CryptoGames.FSAEAD.Costed.rrDecM, fsRrDec]

theorem prgRedZero_inst_coinSimEquiv (qR j : ℕ)
    (hℓ : ℓ < 10 ^ 6) (hj : j ≤ 2 * (qR + maxForwardJumps + 1))
    (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : CryptoGames.FSAEAD.MakesAtMostQueries A qR) (mt : BitVec 256 × BitVec 256) :
    CoinSimEquiv (coinOnlyBaseIface ℓ Pt).fwdU
      (evalTwoStage1 ((fsCostedRedsInst C codec ℓ encT idOf qR).prgRedZero j) qR false
        (fun _ => pubToADCosted (fsCostedRedsInst C codec ℓ encT idOf qR) A) mt)
      (CryptoGames.FSAEAD.Thm5.cumulativeChainPrgReduction
        (lIdeal C clampedProtoSignalCodec ℓ encT)
        (lAeadR C clampedProtoSignalCodec ℓ encT idOf)
        (lChainPRG C.F) maxForwardJumps j (pubToAD clampedProtoSignalCodec A) mt) := by
  rw [pubToADCosted_inst_eq C codec ℓ encT idOf qR hℓ A]
  change CoinSimEquiv _
    (evalTwoStage1 ((fsCostedRedsInst C codec ℓ encT idOf qR).prgRedZero j) qR false
      (fun _ => pubToAD clampedProtoSignalCodec A) mt) _
  dsimp only [fsCostedRedsInst, guardTwoStageRed]
  simp only [hℓ, hj, and_self, ↓reduceIte]
  refine (compilePureTwoStageRed_coinSimEquiv (fsaeadRatchetCodec ℓ Pt)
    (prgZeroMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps j)
    rfl rfl (fun _ => rfl) (hybOpMacro_eval C ℓ encT idOf hinj)
    (fun s x => by
      cases s with
      | inl s =>
        cases s with
        | inl e => exact nomatch e
        | inr u =>
          cases u; rcases x with ⟨i, a⟩
          refine (sampleIdealComp_coinSimEquiv ℓ Pt C encT (I := coinOnlyBaseIface ℓ Pt)
            (fun b => Comp.sample (I := coinOnlyBaseIface ℓ Pt) (UniformSamplerTag.base b) .unit)
            (fun b _ => by cases b <;> rfl) (i, fig8PubAdV a)).trans (CoinSimEquiv.of_eq ?_)
          have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
            simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
          rw [hsl]
          dsimp only [prgZeroMacroBundle, Iface.withSamp, Samplers.sum,
            CryptoGames.PRG.Costed.prgIface, CryptoGames.OTCCA.Costed.idealSamplers,
            coinOnlyBaseIface, Iface.liftP, toVal, hybToDen, hybBaseTy, mapTy,
            CryptoGames.FSAEAD.Costed.bt]
          rfl
      | inr t =>
        rcases t with _ | N | (_ | _)
        · exact CoinSimEquiv.of_eq rfl
        · exact CoinSimEquiv.of_eq (by
            dsimp only [prgZeroMacroBundle, coinOnlyBaseIface, Iface.withSamp, Samplers.sum,
              Sum.elim, CryptoGames.PRG.Costed.prgIface, Iface.liftP, unifSamplers,
              CryptoGames.FSAEAD.Costed.fsStateSampleSort, CryptoGames.FSAEAD.Costed.fsSig,
              Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, AtomicSort.den,
              toVal, hybToDen, hybBaseTy, mapTy]
            exact (id_map _).symm)
        · exact CoinSimEquiv.of_eq rfl
        · exact CoinSimEquiv.of_eq rfl)
    (fun g => nomatch g)
    (fun t => by rcases t with (((((⟨a, m⟩ | ⟨a, m0, m1⟩) | ⟨⟩) | ⟨⟩) | ⟨a, c⟩) | ⟨a, c⟩) <;> rfl)
    (fun t r₁ => hybRdec_eq (Pt := Pt) ℓ t r₁)
    qR false (fun _ => pubToAD clampedProtoSignalCodec A) mt).trans (CoinSimEquiv.of_eq ?_)
  exact CryptoGames.FSAEAD.Thm5.Costed.prgRedZeroProg_eval
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
    (lIdeal C clampedProtoSignalCodec ℓ encT) 1 qR maxForwardJumps j
    (pubToAD clampedProtoSignalCodec A) (isQueryBoundP_pubToAD ℓ hA) mt

theorem multiSlotAdvCosted_inst_coinSimEquiv (qR : ℕ) (la : Bool)
    (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT) (A : FsAdv Pt ℓ)
    (hA : CryptoGames.FSAEAD.MakesAtMostQueries A qR) :
    CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (multiSlotAdvCosted qR (fsCostedRedsInst C codec ℓ encT idOf qR) la A)
      (multiSlotAdv C clampedProtoSignalCodec ℓ encT idOf qR la A) := by
  unfold multiSlotAdvCosted
  rw [pubToADCosted_inst_eq C codec ℓ encT idOf qR hℓ A]
  change CoinSimEquiv _
    (evalTwoStage1 ((fsCostedRedsInst C codec ℓ encT idOf qR).multiRed la) qR false
      (fun _ => pubToAD clampedProtoSignalCodec A) ()) _
  dsimp only [fsCostedRedsInst]
  rw [guardTwoStageRed_pos hℓ]
  refine (compilePureTwoStageRed_coinSimEquiv (fsaeadRatchetCodec ℓ Pt)
    (multiMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.FSAEAD.Thm5.Costed.multiRedProg
      (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
      (lIdeal C clampedProtoSignalCodec ℓ encT) 1
      qR maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la)
    rfl rfl (fun _ => rfl) (hybOpMacro_eval C ℓ encT idOf hinj)
    (fun s x => by
      cases s with
      | inl u =>
        cases u; rcases x with ⟨i, a⟩
        refine (sampleIdealComp_coinSimEquiv ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
          (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
          (fun b _ => by cases b <;> rfl) (i, fig8PubAdV a)).trans (CoinSimEquiv.of_eq ?_)
        have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
          simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
        rw [hsl]
        dsimp only [multiMacroBundle, Iface.withSamp, Samplers.sum,
          CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
          slotOtccaTargetIface, Iface.liftP, toVal, hybToDen, hybBaseTy, mapTy,
          CryptoGames.FSAEAD.Costed.bt]
        rfl
      | inr t =>
        rcases t with _ | N | (_ | _)
        · exact CoinSimEquiv.of_eq rfl
        · exact CoinSimEquiv.of_eq (by
            dsimp only [multiMacroBundle, slotOtccaTargetIface, Iface.withSamp, Samplers.sum,
              Sum.elim, CryptoGames.OTCCA.Costed.otccaIface, Iface.liftP, unifSamplers,
              CryptoGames.FSAEAD.Costed.fsStateSampleSort, CryptoGames.FSAEAD.Costed.fsSig,
              Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, AtomicSort.den,
              toVal, hybToDen, hybBaseTy, mapTy]
            exact (id_map _).symm)
        · exact CoinSimEquiv.of_eq rfl
        · exact CoinSimEquiv.of_eq rfl)
    (fun g x => by
      cases g
      · apply CoinSimEquiv.of_eq
        dsimp only [multiMacroBundle, slotOtccaTargetIface, Iface.withSamp,
          CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote,
          Comp.eval, Expr.eval, hybBaseTy, mapTy, toVal, hybToDen, slotAdOfV, id] at x ⊢
        rcases x with ⟨⟨i, a⟩, m⟩
        simp only [env_get_zero, Functor.map_map]
        rw [fig8PubAdOfV_fig8PubAdV]
      · apply CoinSimEquiv.of_eq
        dsimp only [multiMacroBundle, slotOtccaTargetIface, Iface.withSamp,
          CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.FSAEAD.Costed.fsSig,
          CryptoGames.FSAEAD.Costed.bt, Ty.denote,
          Comp.eval, Expr.eval, hybBaseTy, mapTy, toVal, hybToDen, slotAdOfV, id] at x ⊢
        rcases x with ⟨⟨i, a⟩, e⟩
        simp only [env_get_zero, Functor.map_map]
        rw [fig8PubAdOfV_fig8PubAdV, wireSaltCtOfV_wireSaltCtV]
        congr 1; funext r; cases r <;> rfl)
    (fun t => by rcases t with (((((⟨a, m⟩ | ⟨a, m0, m1⟩) | ⟨⟩) | ⟨⟩) | ⟨a, c⟩) | ⟨a, c⟩) <;> rfl)
    (fun t r₁ => hybRdec_eq (Pt := Pt) ℓ t r₁)
    qR false (fun _ => pubToAD clampedProtoSignalCodec A) ()).trans (CoinSimEquiv.of_eq ?_)
  exact CryptoGames.FSAEAD.Thm5.Costed.multiRedProg_eval
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
    (lIdeal C clampedProtoSignalCodec ℓ encT) 1
    qR maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la
    (pubToAD clampedProtoSignalCodec A) (isQueryBoundP_pubToAD ℓ hA)

theorem multiSlotAdv_clamped_queries (qR : ℕ) (la : Bool) (A : FsAdv Pt ℓ)
    (hA : CryptoGames.FSAEAD.MakesAtMostQueries A qR) :
    (multiSlotAdv C clampedProtoSignalCodec ℓ encT idOf qR la A).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR := by
  unfold multiSlotAdv
  rw [← CryptoGames.FSAEAD.Thm5.Costed.multiRedProg_eval
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
    (lIdeal C clampedProtoSignalCodec ℓ encT) 1
    qR maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la
    (pubToAD clampedProtoSignalCodec A) (isQueryBoundP_pubToAD ℓ hA)]
  exact CryptoGames.FSAEAD.Thm5.Costed.multiRedProg_queries
    (lAeadR C clampedProtoSignalCodec ℓ encT idOf) (lChainPRG C.F) 1 1
    (lIdeal C clampedProtoSignalCodec ℓ encT) 1
    qR maxForwardJumps (if la then qR + (maxForwardJumps + 1) else qR) la
    (pubToAD clampedProtoSignalCodec A) (isQueryBoundP_pubToAD ℓ hA)

end HybBridges

section SaltWireBridges

variable {Pt : Type} [DecidableEq Pt]
  (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey)

private lemma swOpMacro_eval (hinj : Function.Injective encT) (o) (x) :
    (swOpMacro (Pt := Pt) C ℓ encT idOf o).eval (.cons (toVal swBaseTy swToDen _ x) .nil) =
    toVal swBaseTy swToDen _
      ((CryptoGames.AEAD.Costed.saltWireOps C clampedProtoSignalCodec ℓ encT idOf 1).eval o x) := by
  rcases o with (_ | _ | _ | _ | _ | _ | _) | ((_ | _ | _ | _ | _ | _ | _) | (_ | _ | _ | _))
  · rcases x with ⟨mk, ⟨i, a⟩, m⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.libsignalAeadKeyIndexedAd, id]
    rw [aeadKEncExpr_eval]
    simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV, wireSaltCtV, salt32V]
  · rcases x with ⟨mk, ⟨i, a⟩, e⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim,
      CryptoGames.OTCCA.Costed.otccaOps, CryptoGames.AEAD.Costed.libsignalAeadKeyIndexedAd, id]
    rw [aeadKDecExpr_eval]
    have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    have hct : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((e.1.1, e.1.2), salt32V e.2) = e := by
      rcases e with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [hsl, hct]
    cases (lAeadK C clampedProtoSignalCodec ℓ encT idOf).dec mk ((i, a.1), a.2) e <;> rfl
  · rcases x with ⟨i, a⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [saltOfSlotAdExpr_eval]
    simp [Expr.eval, env_get_zero, slotAdOfV, fig8PubAdOfV_fig8PubAdV, salt32V]
  · rcases x with ⟨⟨i₁, a₁⟩, ⟨i₂, a₂⟩⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSlotAdExpr_eval ℓ Pt C encT hinj]
    simp only [Expr.eval, env_get_zero, slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    by_cases h : (i₁, a₁) = (i₂, a₂) <;> simp [h]
  · rcases x with ⟨m₁, m₂⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqPlainExpr_eval]; simp only [Expr.eval, env_get_zero]
    by_cases h : m₁ = m₂ <;> simp [h]
  · rcases x with ⟨c₁, c₂⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqWireSaltCtExpr_eval]
    have hc₁ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₁.1.1, c₁.1.2), salt32V c₁.2) = c₁ := by
      rcases c₁ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    have hc₂ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₂.1.1, c₂.1.2), salt32V c₂.2) = c₂ := by
      rcases c₂ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [Expr.eval, env_get_zero, hc₁, hc₂]
    by_cases h : c₁ = c₂ <;> simp [h]
  · rcases x with ⟨s₁, s₂⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSaltExpr_eval]; simp [Expr.eval, env_get_zero, salt32OfV_salt32V]
  · rcases x with ⟨seed, ⟨i, a⟩, m⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [aeadREncExpr_eval]
    simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV, wireSaltCtV, salt32V]
  · rcases x with ⟨seed, ⟨i, a⟩, e⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [aeadRDecExpr_eval]
    have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    have hct : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((e.1.1, e.1.2), salt32V e.2) = e := by
      rcases e with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [hsl, hct]
    cases (lAeadR C clampedProtoSignalCodec ℓ encT idOf).dec seed (i, a) e <;> rfl
  · rcases x with ⟨i, a⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [saltOfSlotAdExpr_eval]
    simp [Expr.eval, env_get_zero, slotAdOfV, fig8PubAdOfV_fig8PubAdV, salt32V]
  · rcases x with ⟨⟨i₁, a₁⟩, ⟨i₂, a₂⟩⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSlotAdExpr_eval ℓ Pt C encT hinj]
    simp only [Expr.eval, env_get_zero, slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    by_cases h : (i₁, a₁) = (i₂, a₂) <;> simp [h]
  · rcases x with ⟨m₁, m₂⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqPlainExpr_eval]; simp only [Expr.eval, env_get_zero]
    by_cases h : m₁ = m₂ <;> simp [h]
  · rcases x with ⟨c₁, c₂⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqWireSaltCtExpr_eval]
    have hc₁ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₁.1.1, c₁.1.2), salt32V c₁.2) = c₁ := by
      rcases c₁ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    have hc₂ : wireSaltCtOfV (ℓ := ℓ) (Pt := Pt) ((c₂.1.1, c₂.1.2), salt32V c₂.2) = c₂ := by
      rcases c₂ with ⟨⟨w, tg⟩, s⟩; simp [wireSaltCtOfV, salt32OfV_salt32V]
    simp only [Expr.eval, env_get_zero, hc₁, hc₂]
    by_cases h : c₁ = c₂ <;> simp [h]
  · rcases x with ⟨s₁, s₂⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      Ops.sum, Sum.elim, CryptoGames.OTCCA.Costed.otccaOps, id]
    rw [eqSaltExpr_eval]; simp [Expr.eval, env_get_zero, salt32OfV_salt32V]
  · rcases x with ⟨i, ⟨t, T?⟩, pub⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, Ops.sum, Sum.elim, CryptoGames.AEAD.Costed.wireOps,
      fig8PubAdV, id]
    rw [lIdsExpr_eval]; simp [Expr.eval, env_get_zero]
  · rcases x with ⟨i, a⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      CryptoGames.AEAD.Costed.slotAdTy, Ops.sum, Sum.elim, CryptoGames.AEAD.Costed.wireOps, id]
    rw [lHeaderExpr_eval]; simp [Expr.eval, env_get_zero, slotAdOfV, fig8PubAdOfV_fig8PubAdV]
  · rcases x with ⟨h₁, h₂⟩
    dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      Ops.sum, Sum.elim, CryptoGames.AEAD.Costed.wireOps, id]
    rw [eqWireSignalHdrExpr_eval]
    simp only [Expr.eval, env_get_zero, wireSignalHdrOfV_wireSignalHdrV]
  · dsimp only [swOpMacro, swBaseTy, swToDen, mapTy, toVal, CryptoGames.AEAD.Costed.saltWireOps,
      Ops.sum, Sum.elim, CryptoGames.AEAD.Costed.wireOps, id]
    rw [fitPlainExpr_eval]; rfl

omit [DecidableEq Pt] in
private lemma swRdec_eq (t) (r₁) :
    (ReductionDsl.slotOtccaCodec ℓ Pt).rdec t
      (toVal swBaseTy swToDen (CryptoGames.AEAD.Costed.slotOtccaCodec Pt ℓ).R r₁) =
    (CryptoGames.AEAD.Costed.slotOtccaCodec Pt ℓ).rdec t r₁ := by
  cases t
  · rcases r₁ with (_ | ⟨⟨w, tg⟩, s⟩) | r
    · rfl
    · simp [CryptoGames.AEAD.Costed.slotOtccaCodec,
        CryptoGames.AEAD.Costed.lctTy, CryptoGames.AEAD.Costed.wireTagTy,
        CryptoGames.OTCCA.Costed.otccaCodec, swBaseTy, mapTy, toVal, swToDen,
        wireSaltCtOfV, salt32OfV_salt32V]
    · rfl
  · rcases r₁ with l | (_ | m) <;> rfl

private lemma slotSwSamp_coinSimEquiv (s) (x) :
    CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).sampMacro s).eval
        (.cons (toVal swBaseTy swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).smp.sDom s) x) .nil))
      (toVal (swBaseTy (Pt := Pt) (ℓ := ℓ)) swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).smp.sTy s) <$>
        (CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).liftP
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).smp.samp s x)) := by
  cases s with
  | inl u =>
    cases u; rcases x with ⟨i, a⟩
    refine (sampleIdealComp_coinSimEquiv ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
      (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
      (fun b _ => by cases b <;> rfl) (i, fig8PubAdV a)).trans (CoinSimEquiv.of_eq ?_)
    have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
      simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
    rw [hsl]
    dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp,
      Samplers.sum, CryptoGames.OTCCA.Costed.otccaIface, CryptoGames.OTCCA.Costed.idealSamplers,
      slotOtccaTargetIface, Iface.liftP, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, swBaseTy, mapTy, toVal, swToDen, wireSaltCtV, salt32V]
    rfl
  | inr t =>
    rcases t with _ | N | (_ | _)
    · exact CoinSimEquiv.of_eq (by
        simp [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
          CryptoGames.OTCCA.Costed.otccaIface, Iface.withSamp, Samplers.sum,
          Iface.liftP, unifSamplers, Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort,
          swBaseTy, mapTy, toVal])
    · exact CoinSimEquiv.of_eq (by
        simp [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
          CryptoGames.OTCCA.Costed.otccaIface, Iface.withSamp, Samplers.sum,
          Iface.liftP, unifSamplers, Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort,
          swBaseTy, mapTy, toVal])
    · refine (sampleMsgKeyComp_coinSimEquiv ℓ Pt C encT (I := slotOtccaTargetIface ℓ Pt)
        (fun b => Comp.sample (I := slotOtccaTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
        (fun b _ => by cases b <;> rfl) _).trans (CoinSimEquiv.of_eq ?_)
      dsimp only [slotSwMacroBundle, CryptoGames.AEAD.Costed.slotOtccaIface, Iface.withSamp,
        Samplers.sum, CryptoGames.OTCCA.Costed.otccaIface, slotOtccaTargetIface, Iface.liftP,
        unifSamplers, CryptoGames.AEAD.Costed.slotKeySort, swBaseTy, mapTy, toVal, swToDen]
      rfl
    · exact CoinSimEquiv.of_eq (by
        dsimp only [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
          CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
          CryptoGames.OTCCA.Costed.otccaIface, Iface.withSamp, Samplers.sum, Sum.elim,
          Iface.liftP, unifSamplers, CryptoGames.AEAD.Costed.slotKeySort, Comp.eval,
          atomicBaseSamplers, AtomicBaseUnif.sort, AtomicSort.den, swBaseTy, mapTy, toVal, swToDen]
        simp only [id_map]; rfl)

private lemma slotSwQuery_coinSimEquiv (g) (x) :
    CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (((slotSwMacroBundle (Pt := Pt) C ℓ encT idOf).queryMacro g).eval
        (.cons (toVal swBaseTy swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).dom g) x) .nil))
      (toVal (swBaseTy (Pt := Pt) (ℓ := ℓ)) swToDen
          ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).cod g) <$>
        ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).dec g x <$>
          liftM ((unifSpec + AEADScheme.otccaSpec _ _ _).query
            ((CryptoGames.AEAD.Costed.slotOtccaIface C clampedProtoSignalCodec ℓ encT 1).enc g x)))) := by
  cases g
  · apply CoinSimEquiv.of_eq
    dsimp only [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
      CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface,
      Ty.denote, Comp.eval, Expr.eval, swBaseTy, mapTy, toVal, swToDen, slotAdOfV, id] at x ⊢
    rcases x with ⟨⟨i, a⟩, m⟩
    simp only [env_get_zero, Functor.map_map]
    rw [fig8PubAdOfV_fig8PubAdV]
    congr 1
  · apply CoinSimEquiv.of_eq
    dsimp only [slotSwMacroBundle, slotOtccaTargetIface, CryptoGames.AEAD.Costed.slotOtccaIface,
      CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
      CryptoGames.AEAD.Costed.slotAdTy, CryptoGames.AEAD.Costed.lctTy,
      CryptoGames.AEAD.Costed.wireTagTy, Iface.withSamp, CryptoGames.OTCCA.Costed.otccaIface,
      Ty.denote, Comp.eval, Expr.eval, swBaseTy, mapTy, toVal, swToDen, slotAdOfV, wireSaltCtOfV,
      id] at x ⊢
    rcases x with ⟨⟨i, a⟩, ⟨⟨w, tg⟩, s⟩⟩
    simp only [env_get_zero, Functor.map_map]
    rw [fig8PubAdOfV_fig8PubAdV, salt32OfV_salt32V]
    congr 1; funext r
    cases r <;> rfl

theorem slotSaltRed_inst_coinSimEquiv (qR j : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hj : j ≤ 2 * (qR + maxForwardJumps + 1)) (hinj : Function.Injective encT)
    (B : AEADScheme.OTCCAAdversary
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR) :
    CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (((fsCostedRedsInst C codec ℓ encT idOf qR).slotSaltRed j).eval (fun _ => B) ())
      (slotSaltRed C clampedProtoSignalCodec ℓ encT idOf
        (if CryptoGames.FSAEAD.Thm5.isLookaheadHop j then qR + (maxForwardJumps + 1) else qR)
        (j / 2) B) := by
  dsimp only [fsCostedRedsInst]
  simp only [hℓ, hj, and_self, ↓reduceIte]
  refine (compilePureRed_coinSimEquiv (ReductionDsl.slotOtccaCodec ℓ Pt)
    (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltRedProg
      C clampedProtoSignalCodec ℓ encT idOf 1 1
      (if CryptoGames.FSAEAD.Thm5.isLookaheadHop j then qR + (maxForwardJumps + 1) else qR)
      (j / 2) qR)
    rfl rfl (fun _ => rfl) (swOpMacro_eval C ℓ encT idOf hinj)
    (slotSwSamp_coinSimEquiv C ℓ encT idOf) (slotSwQuery_coinSimEquiv C ℓ encT idOf)
    (fun t => by rcases t with ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, ⟨⟨w, tg⟩, s⟩⟩ <;> rfl)
    (fun t r₁ => swRdec_eq (Pt := Pt) ℓ t r₁)
    (fun _ => B) ()).trans (CoinSimEquiv.of_eq ?_)
  exact CryptoGames.Ratchet.LibsignalInst.Costed.slotSaltRedProg_eval
    C clampedProtoSignalCodec ℓ encT idOf 1 1
    (if CryptoGames.FSAEAD.Thm5.isLookaheadHop j then qR + (maxForwardJumps + 1) else qR)
    (j / 2) qR B hB

theorem lSaltRed_inst_coinSimEquiv (qR : ℕ) (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (B : AEADScheme.OTCCAAdversary
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt) :
    CoinSimEquiv (saltPrfTargetIface ℓ Pt).fwdU
      ((fsCostedRedsInst C codec ℓ encT idOf qR).lSaltRed.eval (fun _ => B) ())
      (lSaltRed C clampedProtoSignalCodec ℓ encT idOf B) := by
  dsimp only [fsCostedRedsInst]
  simp only [hℓ, ↓reduceIte]
  refine (compilePureRed_coinSimEquiv (ReductionDsl.slotOtccaCodec ℓ Pt)
    (lSaltMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.lSaltRedProg C clampedProtoSignalCodec ℓ encT idOf 1 1)
    rfl rfl (fun _ => rfl) (swOpMacro_eval C ℓ encT idOf hinj)
    (fun s x => by
      cases s with
      | inl s =>
        cases s with
        | inl e => exact nomatch e
        | inr u =>
          cases u; rcases x with ⟨i, a⟩
          refine (sampleIdealComp_coinSimEquiv ℓ Pt C encT (I := saltPrfTargetIface ℓ Pt)
            (fun b => Comp.sample (I := saltPrfTargetIface ℓ Pt) (UniformSamplerTag.base b) .unit)
            (fun b _ => by cases b <;> rfl) (i, fig8PubAdV a)).trans (CoinSimEquiv.of_eq ?_)
          have hsl : slotAdOfV (ℓ := ℓ) (Pt := Pt) (i, fig8PubAdV (ℓ := ℓ) (Pt := Pt) a) = (i, a) := by
            simp [slotAdOfV, fig8PubAdOfV_fig8PubAdV]
          rw [hsl]
          dsimp only [lSaltMacroBundle, CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp,
            Samplers.sum, CryptoGames.OTCCA.Costed.idealSamplers, CryptoGames.PRF.Costed.prfIface,
            saltPrfTargetIface, Iface.liftP, CryptoGames.AEAD.Costed.lctTy,
            CryptoGames.AEAD.Costed.wireTagTy, swBaseTy, mapTy, toVal, swToDen, wireSaltCtV,
            salt32V]
          rfl
      | inr t =>
        rcases t with _ | N | e
        · exact CoinSimEquiv.of_eq (by
            simp [lSaltMacroBundle, saltPrfTargetIface,
              CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp, Samplers.sum,
              CryptoGames.PRF.Costed.prfIface, Iface.liftP, unifSamplers, unifSamplers0,
              Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, swBaseTy, mapTy, toVal])
        · exact CoinSimEquiv.of_eq (by
            simp [lSaltMacroBundle, saltPrfTargetIface,
              CryptoGames.AEAD.Costed.saltRedIface, Iface.withSamp, Samplers.sum,
              CryptoGames.PRF.Costed.prfIface, Iface.liftP, unifSamplers, unifSamplers0,
              Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, swBaseTy, mapTy, toVal])
        · exact nomatch e)
    (fun g x => by
      cases g
      apply CoinSimEquiv.of_eq
      dsimp only [lSaltMacroBundle, saltPrfTargetIface, CryptoGames.AEAD.Costed.saltRedIface,
        CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
        Iface.withSamp, CryptoGames.PRF.Costed.prfIface, Ty.denote, Comp.eval, Expr.eval,
        swBaseTy, mapTy, toVal, swToDen, id] at x ⊢
      simp only [env_get_zero, Functor.map_map]
      rw [salt32OfV_salt32V])
    (fun t => by rcases t with ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, ⟨⟨w, tg⟩, s⟩⟩ <;> rfl)
    (fun t r₁ => swRdec_eq (Pt := Pt) ℓ t r₁)
    (fun _ => B) ()).trans (CoinSimEquiv.of_eq ?_)
  exact CryptoGames.Ratchet.LibsignalInst.Costed.lSaltRedProg_eval
    C clampedProtoSignalCodec ℓ encT idOf 1 1 B

theorem slotWireRed_inst_coinSimEquiv (qR j : ℕ) (hℓ : ℓ < 10 ^ 6)
    (hj : j ≤ 2 * (qR + maxForwardJumps + 1)) (hinj : Function.Injective encT)
    (B : AEADScheme.OTCCAAdversary
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR) :
    CoinSimEquiv (slotOtccaTargetIface ℓ Pt).fwdU
      (((fsCostedRedsInst C codec ℓ encT idOf qR).slotWireRed j).eval (fun _ => B) ())
      (slotWireRed C clampedProtoSignalCodec ℓ encT idOf (j / 2) B) := by
  dsimp only [fsCostedRedsInst]
  simp only [hℓ, hj, and_self, ↓reduceIte]
  refine (compilePureRed_coinSimEquiv (ReductionDsl.slotOtccaCodec ℓ Pt)
    (slotSwMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.slotWireRedProg
      C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2) qR)
    rfl rfl (fun _ => rfl) (swOpMacro_eval C ℓ encT idOf hinj)
    (slotSwSamp_coinSimEquiv C ℓ encT idOf) (slotSwQuery_coinSimEquiv C ℓ encT idOf)
    (fun t => by rcases t with ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, ⟨⟨w, tg⟩, s⟩⟩ <;> rfl)
    (fun t r₁ => swRdec_eq (Pt := Pt) ℓ t r₁)
    (fun _ => B) ()).trans (CoinSimEquiv.of_eq ?_)
  exact CryptoGames.Ratchet.LibsignalInst.Costed.slotWireRedProg_eval
    C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2) qR B hB

theorem slotWireRed_clamped_queries (qR j : ℕ)
    (B : AEADScheme.OTCCAAdversary
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR) :
    (slotWireRed C clampedProtoSignalCodec ℓ encT idOf (j / 2) B).IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR := by
  rw [← CryptoGames.Ratchet.LibsignalInst.Costed.slotWireRedProg_eval
    C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2) qR B hB]
  exact CryptoGames.Ratchet.LibsignalInst.Costed.slotWireRedProg_queries
    C clampedProtoSignalCodec ℓ encT idOf 1 1 (j / 2) qR B hB

theorem lWireRed_inst_coinSimEquiv (qR : ℕ) (hℓ : ℓ < 10 ^ 6) (hinj : Function.Injective encT)
    (B : AEADScheme.OTCCAAdversary
      (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)
    (hB : B.IsQueryBoundP
      (isGameQuery (G := AEADScheme.otccaSpec
        (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LCt)) qR) :
    CoinSimEquiv (wireOtccaTargetIface ℓ Pt).fwdU
      ((fsCostedRedsInst C codec ℓ encT idOf qR).lWireRed.eval (fun _ => B) ())
      (lWireRed C clampedProtoSignalCodec ℓ encT idOf 0 B) := by
  dsimp only [fsCostedRedsInst]
  simp only [hℓ, ↓reduceIte]
  refine (compilePureRed_coinSimEquiv (ReductionDsl.slotOtccaCodec ℓ Pt)
    (lWireMacroBundle (Pt := Pt) C ℓ encT idOf)
    (CryptoGames.Ratchet.LibsignalInst.Costed.lWireRedProg
      C clampedProtoSignalCodec ℓ encT idOf 1 0 qR)
    rfl rfl (fun _ => rfl) (swOpMacro_eval C ℓ encT idOf hinj)
    (fun s x => by
      cases s with
      | inl e => exact nomatch e
      | inr t =>
        rcases t with _ | N | e
        · exact CoinSimEquiv.of_eq (by
            simp [lWireMacroBundle, wireOtccaTargetIface,
              CryptoGames.AEAD.Costed.wireRedIface, Iface.withSamp, Samplers.sum,
              CryptoGames.AEAD.Costed.wireIface, Iface.liftP, unifSamplers, unifSamplers0,
              Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, swBaseTy, mapTy, toVal])
        · exact CoinSimEquiv.of_eq (by
            simp [lWireMacroBundle, wireOtccaTargetIface,
              CryptoGames.AEAD.Costed.wireRedIface, Iface.withSamp, Samplers.sum,
              CryptoGames.AEAD.Costed.wireIface, Iface.liftP, unifSamplers, unifSamplers0,
              Comp.eval, atomicBaseSamplers, AtomicBaseUnif.sort, swBaseTy, mapTy, toVal])
        · exact nomatch e)
    (fun g x => by
      cases g
      · apply CoinSimEquiv.of_eq
        dsimp only [lWireMacroBundle, wireOtccaTargetIface, CryptoGames.AEAD.Costed.wireRedIface,
          CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
          Iface.withSamp, CryptoGames.AEAD.Costed.wireIface, Ty.denote, Comp.eval, Expr.eval,
          swBaseTy, mapTy, toVal, swToDen, id] at x ⊢
        rcases x with ⟨ad, h, m⟩
        simp only [env_get_zero, Functor.map_map]
        rw [fitBytesN_toList, wireSignalHdrOfV_wireSignalHdrV]
        congr 1; funext r
        rcases r with _ | ⟨w, tg⟩ <;> rfl
      · apply CoinSimEquiv.of_eq
        dsimp only [lWireMacroBundle, wireOtccaTargetIface, CryptoGames.AEAD.Costed.wireRedIface,
          CryptoGames.AEAD.Costed.saltWireSig, CryptoGames.AEAD.Costed.SaltWireSort.den,
          Iface.withSamp, CryptoGames.AEAD.Costed.wireIface, Ty.denote, Comp.eval, Expr.eval,
          swBaseTy, mapTy, toVal, swToDen, id] at x ⊢
        rcases x with ⟨ad, w, tg⟩
        simp only [env_get_zero, Functor.map_map]
        rw [fitBytesN_toList])
    (fun t => by rcases t with ⟨⟨i, a⟩, m⟩ | ⟨⟨i, a⟩, ⟨⟨w, tg⟩, s⟩⟩ <;> rfl)
    (fun t r₁ => swRdec_eq (Pt := Pt) ℓ t r₁)
    (fun _ => B) ()).trans (CoinSimEquiv.of_eq ?_)
  exact CryptoGames.Ratchet.LibsignalInst.Costed.lWireRedProg_eval
    C clampedProtoSignalCodec ℓ encT idOf 1 0 qR B hB

end SaltWireBridges

end Computational.Proofs.ReductionDsl.FsAtomicSoundness
