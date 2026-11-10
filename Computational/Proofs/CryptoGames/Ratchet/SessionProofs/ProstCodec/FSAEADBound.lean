/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.FSAEAD.Theorem5On
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.WireHop
public import Computational.Proofs.CryptoGames.SM.ReductionsQueries
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.IndexRestrictions
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.MsgAeadCorrect
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.PubToAD
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.WireHop.Helpers
import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.SaltHop
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Composed FS-AEAD bound for short public parts

**Checked by Lean.**

Proves `lFS_full_bound_short_proof` by composing the restricted pub-to-AD reduction, multi-slot
ACD19 Theorem 5 (`theorem5With_on_multi`), per-slot salt-PRF and wire OT-CCA hops, and one global
MAC-forgery hop per chain.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames.LibsignalSM.Proofs.ProstFSAEADBound

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

variable {Pt : Type}

/-! ## Query-bound preservation -/

theorem isQueryBoundP_slotWireRed [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    {Q : (FSAEAD.Thm5.IndexedOtccaSpec (Header Pt × LibsignalMsgPublicPart) (Plain ℓ) LibsignalCiphertextWithSalt32).Domain → Prop} [DecidablePred Q]
    (hQu : ∀ u, ¬ Q (.inl u)) {n : ℕ} (hn : B.IsQueryBoundP Q n) :
    (slotWireRed C codec ℓ encT idOf k B).IsQueryBoundP Q n := by
  unfold slotWireRed
  exact (isQueryBoundP_map_iff _ _ _).mpr
    (FSAEAD.Thm5.slotRedImpl_isQueryBoundP
      (slotSaltImplNF C codec ℓ encT idOf false)
      (slotSaltImpl C codec ℓ encT idOf true) k hQu B
      (fun _ => {}, fun _ => {}) hn)

theorem slotWireRed_adClassConst [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hcls : AEADScheme.OTAllQueriesInOneADClass lCls B) :
    AEADScheme.OTAllQueriesInOneADClass lCls (slotWireRed C codec ℓ encT idOf k B) := by
  rcases hcls with ⟨k₀, hk₀⟩
  exact ⟨k₀, isQueryBoundP_slotWireRed C codec ℓ encT idOf k B
    (fun u => by simp [AEADScheme.otQueryADOutsideClass]) hk₀⟩

theorem slotWireRed_encADsOk [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hshort : AEADScheme.OTEncADsOk (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) B) :
    AEADScheme.OTEncADsOk (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB)
      (slotWireRed C codec ℓ encT idOf k B) :=
  isQueryBoundP_slotWireRed C codec ℓ encT idOf k B
    (fun u => by simp [AEADScheme.otEncBad]) hshort

theorem slotWireRed_badIdx [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) {k : ℕ} (hk : k < 2 ^ 32)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    (slotWireRed C codec ℓ encT idOf k B).IsQueryBoundP
      (fun t => WireHop.otBadIdx (Pt := Pt) (ℓ := ℓ) t = true) 0 := by
  unfold slotWireRed
  refine (isQueryBoundP_map_iff _ _ _).mpr ?_
  exact FSAEAD.Thm5.slotRedImpl_zero_of_slot
    (slotSaltImplNF C codec ℓ encT idOf false)
    (slotSaltImpl C codec ℓ encT idOf true) k
    (fun u => by simp [WireHop.otBadIdx])
    (fun a m => by simp only [WireHop.otBadIdx, decide_eq_true_eq]; omega)
    (fun a e => by simp only [WireHop.otBadIdx, decide_eq_true_eq]; omega)
    B (fun _ => {}, fun _ => {})

theorem multiRedWith_otADClassConst {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    {κ : Type} [DecidableEq κ] (cls : AD → κ)
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ) (la : Bool)
    (A : FSAEAD.RatchetAdversary CK MK AD M C) (hcls : FSAEAD.AllQueriesInOneADClass cls A) :
    AEADScheme.OTAllQueriesInOneADClass (fun ia : ℕ × AD => cls ia.2)
      (FSAEAD.Thm5.multiSlotOtccaReduction ideal ae G maxSkip N la A) := by
  rcases hcls with ⟨k₀, hk₀⟩
  refine ⟨k₀, FSAEAD.Thm5.multiRedWith_zero_of_zero ideal ae G maxSkip
    (fun u => by simp [AEADScheme.otQueryADOutsideClass]) N la A hk₀ ?_ ?_ ?_⟩
  · intro a m hnp i _ _
    simpa [AEADScheme.otQueryADOutsideClass, FSAEAD.queryADOutsideClass] using hnp
  · intro a m₀ m₁ hnp i _ _ m
    simpa [AEADScheme.otQueryADOutsideClass, FSAEAD.queryADOutsideClass] using hnp
  · intro a i e hnp _ _
    simpa [AEADScheme.otQueryADOutsideClass, FSAEAD.queryADOutsideClass] using hnp

theorem multiRedWith_otEncADsOk {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ok : AD → Bool)
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ) (la : Bool)
    (A : FSAEAD.RatchetAdversary CK MK AD M C) (hA : FSAEAD.EncADsOk ok A) :
    AEADScheme.OTEncADsOk (fun ia : ℕ × AD => ok ia.2)
      (FSAEAD.Thm5.multiSlotOtccaReduction ideal ae G maxSkip N la A) :=
  FSAEAD.Thm5.multiRedWith_zero_of_zero ideal ae G maxSkip
    (fun u => by simp [AEADScheme.otEncBad]) N la A hA
    (fun a m hnp _ _ _ => by simpa [AEADScheme.otEncBad, FSAEAD.encBadAD] using hnp)
    (fun a m₀ m₁ hnp _ _ _ m => by simpa [AEADScheme.otEncBad, FSAEAD.encBadAD] using hnp)
    (fun _ _ _ _ _ _ => by simp [AEADScheme.otEncBad])

theorem multiRedWith_makesAtMostDecQueries {CK MK AD M C : Type} [SampleableType MK] [SampleableType CK]
    [DecidableEq AD] [DecidableEq M] [DecidableEq C]
    (ideal : ℕ × AD → ProbComp C) (ae : AEADScheme MK (ℕ × AD) M C)
    (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip N : ℕ) (la : Bool)
    (A : FSAEAD.RatchetAdversary CK MK AD M C) {qd : ℕ}
    (hqd : FSAEAD.MakesAtMostDecQueries A qd) :
    MakesAtMostDecQueries (FSAEAD.Thm5.multiSlotOtccaReduction ideal ae G maxSkip N la A) qd := by
  have h := FSAEAD.Thm5.multiRedWith_le_of_step ideal ae G maxSkip
    (Q := fun t => isDecQuery t = true)
    (fun u => by simp [isDecQuery]) N la A qd hqd
    (fun _ _ _ _ _ => by simp [isDecQuery])
    (fun _ => by simp [FSAEAD.isDecQuery])
    (fun _ _ => by simp [FSAEAD.isDecQuery])
    (fun _ _ _ => by simp [FSAEAD.isDecQuery])
    (fun _ => by simp [FSAEAD.isDecQuery])
    (fun _ => by simp [FSAEAD.isDecQuery])
    (fun _ _ => by simp [FSAEAD.isDecQuery])
    (fun _ _ => by simp [FSAEAD.isDecQuery])
  simpa [MakesAtMostDecQueries] using h

theorem pubRed_guardedFSInjectShort {SS RS AD Pub M : Type}
    (pubOf : ℕ × LibsignalCiphertextWithSalt32 → Option Pub)
    (A : FSAEAD.Adversary SS RS AD (Pub × M) (ℕ × LibsignalCiphertextWithSalt32))
    (hA : GuardedFSInjectShort A) :
    GuardedFSInjectShort (FSAEAD.pubRed pubOf A) := by
  unfold FSAEAD.pubRed GuardedFSInjectShort
  rw [StateT.run'_eq]
  refine GuardedSafe.GuardedSafePost.map (P := fun _ => True) Prod.fst ?_ (fun _ _ => trivial)
  refine GuardedSafe.GuardedSafePost.simulateQ_run (I := fun _ : Bool => True) hA ?_ trivial
  intro t ht
  rcases t with n | (((((⟨a, pm⟩ | ⟨a, pm₀, pm₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, i, e⟩)
  · intro _ _; dsimp only [FSAEAD.pubRedImpl]; rw [StateT.run_lift]
    exact (GuardedSafe.GuardedSafePost.query (by simp [fsInjectLong])).bind fun a ha =>
      GuardedSafe.GuardedSafePost.pure ⟨ha, trivial⟩
  · intro _ _; dsimp only [FSAEAD.pubRedImpl, FSAEAD.transmitQuery]; rw [StateT.run_lift]
    exact (GuardedSafe.GuardedSafePost.query (by simp [fsInjectLong])).bind fun a ha =>
      GuardedSafe.GuardedSafePost.pure ⟨ha, trivial⟩
  · intro _ _; dsimp only [FSAEAD.pubRedImpl, FSAEAD.challengeQuery]; rw [StateT.run_lift]
    exact (GuardedSafe.GuardedSafePost.query (by simp [fsInjectLong])).bind fun a ha =>
      GuardedSafe.GuardedSafePost.pure ⟨ha, trivial⟩
  · intro _ _; dsimp only [FSAEAD.pubRedImpl, FSAEAD.corruptSenderQuery]; rw [StateT.run_lift]
    exact (GuardedSafe.GuardedSafePost.query (by simp [fsInjectLong])).bind fun a ha =>
      GuardedSafe.GuardedSafePost.pure ⟨ha, trivial⟩
  · dsimp only [FSAEAD.pubRedImpl, FSAEAD.corruptReceiverQuery]
    refine GuardedSafe.guardedSafeS_bind_query (by simp [fsInjectLong]) fun r _ => ?_
    split_ifs
    · exact GuardedSafe.guardedSafeS_bind_true
        (GuardedSafe.guardedSafeS_set_true true fun _ _ => trivial)
        fun _ => GuardedSafe.guardedSafeS_pure r fun _ _ => ⟨trivial, trivial⟩
    · exact GuardedSafe.guardedSafeS_pure r fun _ _ => ⟨trivial, trivial⟩
  · dsimp only [FSAEAD.pubRedImpl, FSAEAD.deliverQuery]
    cases pubOf c with
    | none => exact GuardedSafe.guardedSafeS_pure none fun _ _ => ⟨trivial, trivial⟩
    | some p =>
      intro _ _
      rw [StateT.run_lift]
      exact ((GuardedSafe.GuardedSafePost.query (by simp [fsInjectLong])).bind fun _ _ =>
        GuardedSafe.GuardedSafePost.pure (P := fun _ => True) trivial).bind fun _ _ =>
        GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩
  · dsimp only [FSAEAD.pubRedImpl, FSAEAD.injectQuery]
    cases pubOf (i, e) with
    | none =>
      exact GuardedSafe.guardedSafeS_get_bind fun ended _ =>
        GuardedSafe.guardedSafeS_pure _ fun _ _ => ⟨trivial, trivial⟩
    | some p =>
      intro _ _
      rw [StateT.run_lift]
      exact ((GuardedSafe.GuardedSafePost.query (by simpa [fsInjectLong] using ht)).bind fun _ _ =>
        GuardedSafe.GuardedSafePost.pure (P := fun _ => True) trivial).bind fun _ _ =>
        GuardedSafe.GuardedSafePost.pure ⟨trivial, trivial⟩

theorem multiEncIdx_guardedSafePost [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (hfit : SignalEncodeFits32 codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (N i : ℕ) (a : Header Pt × LibsignalMsgPublicPart) (msg : Plain ℓ)
    (ha : a.2.shortB = true)
    (s : FSAEAD.Thm5.HSt (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart) (Plain ℓ)
      LibsignalCiphertextWithSalt32) :
    GuardedSafe.GuardedSafePost otRespShort otDecLong
      (fun r => r.1.1.1.length + 8 < 2 ^ 32)
      ((FSAEAD.Thm5.multiEncIdxWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) 0 N
        (some (FSAEAD.Thm5.otOpsWith (lIdeal C codec ℓ encT))) i a msg).run s) := by
  classical
  have hQu : ∀ u, ¬ otDecLong (AD := ℕ × (Header Pt × LibsignalMsgPublicPart)) (M := Plain ℓ) (.inl u) :=
    fun _ => by simp [otDecLong]
  unfold FSAEAD.Thm5.multiEncIdxWith
  rw [StateT.run_bind]
  refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP (FSAEAD.Thm5.qb_getH (Q := otDecLong) s)).bind fun p _ => ?_
  split
  · simp only [FSAEAD.Thm5.sampleH, StateT.run_monadLift]
    exact (ProstMsgAeadCorrect.guardedSafePost_liftM_lIdeal hQu C codec hfit ℓ hℓ encT (i, a) ha).bind
      fun _ he => GuardedSafe.GuardedSafePost.pure he
  · rename_i _ hops
    obtain rfl := Option.some.inj hops
    dsimp only [FSAEAD.Thm5.otOpsWith, StateT.run_monadLift, MonadLiftT.monadLift, MonadLift.monadLift]
    rw [bind_assoc]
    refine (GuardedSafe.GuardedSafePost.query ?_).bind fun r hr => ?_
    · simp [otDecLong]
    · cases r with
      | none =>
        exact (ProstMsgAeadCorrect.guardedSafePost_liftM_lIdeal hQu C codec hfit ℓ hℓ encT (i, a) ha).bind
          fun _ he => GuardedSafe.GuardedSafePost.pure he
      | some e =>
        rw [pure_bind]
        exact GuardedSafe.GuardedSafePost.pure (hr e rfl)
  · split
    · rw [StateT.run_pure]
      exact GuardedSafe.GuardedSafePost.pure
        (ProstMsgAeadCorrect.lAeadK_enc_length_lt C codec hfit ℓ hℓ encT idOf
          (deriveMessageKeys C.F (some a.2.salt) (keyToBytes32 _)) ((i, a.1), a.2) msg ha)
    · simp only [FSAEAD.Thm5.sampleH, StateT.run_monadLift]
      exact (ProstMsgAeadCorrect.guardedSafePost_liftM_lIdeal hQu C codec hfit ℓ hℓ encT (i, a) ha).bind
        fun _ he => GuardedSafe.GuardedSafePost.pure he

theorem multiRedWith_guardedOTDecShort [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (hfit : SignalEncodeFits32 codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip N : ℕ) (la : Bool)
    (A : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt × LibsignalMsgPublicPart)
      (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hA : FSAEAD.EncADsOk (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB) A)
    (hinj : GuardedFSInjectShort A) :
    GuardedOTDecShort (FSAEAD.Thm5.multiSlotOtccaReduction (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip N la A) := by
  classical
  have hQu : ∀ u, ¬ otDecLong (AD := ℕ × (Header Pt × LibsignalMsgPublicPart)) (M := Plain ℓ) (.inl u) :=
    fun _ => by simp [otDecLong]
  have hcomb := hinj.and_isQueryBoundP hA
  unfold GuardedOTDecShort FSAEAD.Thm5.multiSlotOtccaReduction FSAEAD.Thm5.multiRunWith
  refine (GuardedSafe.GuardedSafePost.liftComp_unif hQu ($ᵗ Bool)).bind fun b _ => ?_
  refine (GuardedSafe.GuardedSafePost.simulateQ_run (I := fun _ => True) hcomb ?_ trivial).bind
    fun _ _ => GuardedSafe.GuardedSafePost.pure trivial
  intro t ht s _
  have ht1 : ¬ fsInjectLong t := fun h => ht (Or.inl h)
  have ht2 : ¬ FSAEAD.encBadAD (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB) t = true :=
    fun h => ht (Or.inr h)
  set P := FSAEAD.Thm5.hp N 0 la
  rcases t with u | (((((⟨a, m⟩ | ⟨a, m₀, m₁⟩) | u) | u) | ⟨a, c⟩) | ⟨a, i, e⟩)
  · exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP (FSAEAD.Thm5.qb_sampleH hQu _ s)).mono
      fun _ _ => ⟨trivial, trivial⟩
  · have ha : a.2.shortB = true := by simpa [FSAEAD.encBadAD] using ht2
    change GuardedSafe.GuardedSafePost otRespShort otDecLong _
      ((FSAEAD.Thm5.multiTransmitHWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (lChainPRG C.F) P N (FSAEAD.Thm5.DG (lChainPRG C.F))
        (some (FSAEAD.Thm5.otOpsWith (lIdeal C codec ℓ encT))) (a, m)).run s)
    unfold FSAEAD.Thm5.multiTransmitHWith
    rw [StateT.run_bind]
    refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP (FSAEAD.Thm5.qb_getH (Q := otDecLong) s)).bind fun st _ => ?_
    split_ifs
    · rw [StateT.run_pure]
      exact GuardedSafe.GuardedSafePost.pure ⟨by rintro _ ⟨⟩, trivial⟩
    · rw [StateT.run_bind]
      refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP
        (FSAEAD.Thm5.qb_genUpTo hQu (lChainPRG C.F) P (FSAEAD.Thm5.DG (lChainPRG C.F)) _ st.2)).bind
        fun u1 _ => ?_
      rw [StateT.run_bind]
      refine (multiEncIdx_guardedSafePost C codec hfit ℓ hℓ encT idOf N _ a m ha u1.2).bind
        fun ec hec => ?_
      rw [StateT.run_bind]
      exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP (FSAEAD.Thm5.qb_modifyH (Q := otDecLong) _ ec.2)).bind
        fun u2 _ => by
          rw [StateT.run_pure]
          exact GuardedSafe.GuardedSafePost.pure ⟨by rintro _ ⟨rfl⟩; exact hec, trivial⟩
  · have ha : a.2.shortB = true := by simpa [FSAEAD.encBadAD] using ht2
    change GuardedSafe.GuardedSafePost otRespShort otDecLong _
      ((FSAEAD.Thm5.multiChallengeHWith (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (lChainPRG C.F) P N (FSAEAD.Thm5.DG (lChainPRG C.F))
        (some (FSAEAD.Thm5.otOpsWith (lIdeal C codec ℓ encT))) (a, m₀, m₁)).run s)
    unfold FSAEAD.Thm5.multiChallengeHWith
    rw [StateT.run_bind]
    refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP (FSAEAD.Thm5.qb_getH (Q := otDecLong) s)).bind fun st _ => ?_
    split_ifs
    · rw [StateT.run_pure]
      exact GuardedSafe.GuardedSafePost.pure ⟨by rintro _ ⟨⟩, trivial⟩
    all_goals
      rw [StateT.run_bind]
      refine (GuardedSafe.GuardedSafePost.of_isQueryBoundP
        (FSAEAD.Thm5.qb_genUpTo hQu (lChainPRG C.F) P (FSAEAD.Thm5.DG (lChainPRG C.F)) _ st.2)).bind
        fun u1 _ => ?_
      rw [StateT.run_bind]
      refine (multiEncIdx_guardedSafePost C codec hfit ℓ hℓ encT idOf N _ a _ ha u1.2).bind
        fun ec hec => ?_
      rw [StateT.run_bind]
      exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP (FSAEAD.Thm5.qb_modifyH (Q := otDecLong) _ ec.2)).bind
        fun u2 _ => by
          rw [StateT.run_pure]
          exact GuardedSafe.GuardedSafePost.pure ⟨by rintro _ ⟨rfl⟩; exact hec, trivial⟩
  · exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP
      (FSAEAD.Thm5.qb_corruptSenderH hQu (lChainPRG C.F) P u s)).mono fun _ _ => ⟨trivial, trivial⟩
  · exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP
      (FSAEAD.Thm5.qb_corruptReceiverH hQu (lChainPRG C.F) P u s)).mono fun _ _ => ⟨trivial, trivial⟩
  · have hqb : IsQueryBoundP
        ((FSAEAD.Thm5.multiDeliverH (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip P N
          (FSAEAD.Thm5.DG (lChainPRG C.F)) (some (FSAEAD.Thm5.otOpsWith (lIdeal C codec ℓ encT)))
          (a, c)).run s) otDecLong 0 := by
      unfold FSAEAD.Thm5.multiDeliverH
      refine (FSAEAD.Thm5.qb_bind0 (FSAEAD.Thm5.qb_getH (Q := otDecLong)) fun st => ?_) s
      split_ifs
      · exact fun _ => by simp
      · split
        · exact fun _ => by simp
        · refine FSAEAD.Thm5.qb_bind_r (FSAEAD.Thm5.qb_multiReceiveH_at (lIdeal C codec ℓ encT)
            (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip hQu P N rfl
            (FSAEAD.Thm5.DG (lChainPRG C.F)) _ a c (fun h => nomatch h)) fun r => ?_
          cases r <;> exact FSAEAD.Thm5.qb_bind0 (FSAEAD.Thm5.qb_modifyH (Q := otDecLong) _) fun _ => fun _ => by simp
    exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP hqb).mono fun _ _ => ⟨trivial, trivial⟩
  · have hqb : IsQueryBoundP
        ((FSAEAD.Thm5.multiInjectH (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip P N
          (FSAEAD.Thm5.DG (lChainPRG C.F)) (some (FSAEAD.Thm5.otOpsWith (lIdeal C codec ℓ encT)))
          (a, (i, e))).run s) otDecLong 0 := by
      unfold FSAEAD.Thm5.multiInjectH
      refine (FSAEAD.Thm5.qb_bind0 (FSAEAD.Thm5.qb_getH (Q := otDecLong)) fun st => ?_) s
      split_ifs
      · exact fun _ => by simp
      · refine FSAEAD.Thm5.qb_bind_r (FSAEAD.Thm5.qb_multiReceiveH_at (lIdeal C codec ℓ encT)
          (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip hQu P N rfl
          (FSAEAD.Thm5.DG (lChainPRG C.F)) none a (i, e)
          (fun _ _ _ => by simpa [otDecLong, fsInjectLong] using ht1)) fun r => ?_
        cases r with
        | none => exact fun _ => by simp
        | some _ => exact FSAEAD.Thm5.qb_bind0 (FSAEAD.Thm5.qb_modifyH (Q := otDecLong) _) fun _ => fun _ => by simp
    exact (GuardedSafe.GuardedSafePost.of_isQueryBoundP hqb).mono fun _ _ => ⟨trivial, trivial⟩

/-! ## Multi-slot wire-OT-CCA hybrid -/

def wireHyb [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    ProbComp Bool :=
  Prod.fst <$> (simulateQ
    (FSAEAD.Thm5.hybSlot
      (slotSaltImplNF C codec ℓ encT idOf false)
      (slotSaltImpl C codec ℓ encT idOf true) k) B).run
    (fun _ => {}, fun _ => {})

theorem wireHyb_zero [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    wireHyb C codec ℓ encT idOf 0 B =
      Prod.fst <$> (simulateQ
        (FSAEAD.Thm5.slotLift (slotSaltImplNF C codec ℓ encT idOf false)) B).run
        (fun _ => {}) := by
  unfold wireHyb
  rw [FSAEAD.Thm5.hybSlot_zero, Functor.map_map]

theorem evalDist_wireHyb_self [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (N : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hoff : B.IsQueryBoundP (fun t => FSAEAD.Thm5.multiOffRange N t = true) 0) :
    𝒟[wireHyb C codec ℓ encT idOf N B] =
      𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true N B] := by
  rw [SaltHop.evalDist_multiOtBranch_true_eq_slotLift_slotSaltImpl_true C codec ℓ encT idOf N B]
  unfold wireHyb
  have h := congrArg (Prod.fst <$> ·)
    (FSAEAD.Thm5.hybSlot_eq_slotLift_of_offRange
      (slotSaltImplNF C codec ℓ encT idOf false)
      (slotSaltImpl C codec ℓ encT idOf true) N B hoff (fun _ => {}) (fun _ => {}))
  simpa only [Functor.map_map] using congrArg evalDist h

theorem wireHyb_step_left [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    wireHyb C codec ℓ encT idOf k B =
      WireHop.saltRunNF C codec ℓ encT idOf false (slotWireRed C codec ℓ encT idOf k B) := by
  rw [← SaltHop.slotSaltImplNF_fst_eq_saltRunNF]
  have hinl : ∀ n (s : SaltSlotSt Pt),
      (slotSaltImplNF C codec ℓ encT idOf false (.inl n)).run s =
        (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
          fun u => pure (u, s) := fun n s => by simp [slotSaltImplNF]
  unfold wireHyb slotWireRed
  have hstep := congrArg (Prod.fst <$> ·)
    (FSAEAD.Thm5.hybSlot_step_left
      (slotSaltImplNF C codec ℓ encT idOf false)
      (slotSaltImpl C codec ℓ encT idOf true) hinl k B
      (fun _ => {}) (fun _ => {}) {})
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, Function.update_eq_self] using
    hstep.symm

theorem wireHyb_step_right [DecidableEq Pt] (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (k : ℕ)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32) :
    wireHyb C codec ℓ encT idOf (k + 1) B =
      WireHop.saltRun C codec ℓ encT idOf true (slotWireRed C codec ℓ encT idOf k B) := by
  rw [← SaltHop.slotSaltImpl_fst_eq_saltRun]
  have hinl : ∀ n (s : SaltSlotSt Pt),
      (slotSaltImpl C codec ℓ encT idOf true (.inl n)).run s =
        (liftM (OracleSpec.query (spec := unifSpec) n) : ProbComp (Fin (n + 1))) >>=
          fun u => pure (u, s) := fun n s => by simp [slotSaltImpl]
  unfold wireHyb slotWireRed
  have hstep := congrArg (Prod.fst <$> ·)
    (FSAEAD.Thm5.hybSlot_step_right
      (slotSaltImplNF C codec ℓ encT idOf false)
      (slotSaltImpl C codec ℓ encT idOf true) hinl k B
      (fun _ => {}) (fun _ => {}) {})
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map, Function.update_eq_self] using
    hstep.symm

theorem multiSaltNF_false_boolDist_multiOtBranch_true [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (hrt : SignalRoundTripShort codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < rustLenBound)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) {N : ℕ} (hN : N ≤ 2 ^ 32)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hoff : B.IsQueryBoundP (fun t => FSAEAD.Thm5.multiOffRange N t = true) 0)
    (hcls : AEADScheme.OTAllQueriesInOneADClass lCls B)
    (hshort : AEADScheme.OTEncADsOk (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) B) :
    𝒟[Prod.fst <$> (simulateQ
        (FSAEAD.Thm5.slotLift (slotSaltImplNF C codec ℓ encT idOf false)) B).run
        (fun _ => {})].boolDist
      𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true N B] ≤
    ∑ k ∈ Finset.range N,
      (lWire C codec ℓ).wireOtccaAdvantage
        (lWireRed C codec ℓ encT idOf 0 (slotWireRed C codec ℓ encT idOf k B)) := by
  rw [← wireHyb_zero C codec ℓ encT idOf B,
    ← evalDist_wireHyb_self C codec ℓ encT idOf N B hoff]
  refine (Measure.boolDist_le_sum_range
    (fun k => 𝒟[wireHyb C codec ℓ encT idOf k B]) N).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  have hk32 : k < 2 ^ 32 := lt_of_lt_of_le (Finset.mem_range.mp hk) hN
  rw [wireHyb_step_left C codec ℓ encT idOf k B,
    wireHyb_step_right C codec ℓ encT idOf k B,
    Measure.boolDist_comm,
    WireHop.wireOtccaAdvantage_eq_boolDist,
    WireHop.evalDist_wireBranch_true_zero,
    ProstWireHop.Helpers.evalDist_wireBranch_false C codec ℓ hℓ encT idOf
      (slotWireRed C codec ℓ encT idOf k B) hinj hdum hrt
      (slotWireRed_adClassConst C codec ℓ encT idOf k B hcls)
      (slotWireRed_badIdx C codec ℓ encT idOf hk32 B)
      (slotWireRed_encADsOk C codec ℓ encT idOf k B hshort)]

theorem multiOtBranch_boolDist_le_short [DecidableEq Pt]
    (C : Crypto) (codec : SignalMessageProtoCodec) (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) {N qd : ℕ} (hN : N ≤ 2 ^ 32)
    (B : OTCCAAdversary (ℕ × (Header Pt × LibsignalMsgPublicPart)) (Plain ℓ) LibsignalCiphertextWithSalt32)
    (hoff : B.IsQueryBoundP (fun t => FSAEAD.Thm5.multiOffRange N t = true) 0)
    (hqd : MakesAtMostDecQueries B qd)
    (hcls : AEADScheme.OTAllQueriesInOneADClass lCls B)
    (hshort : AEADScheme.OTEncADsOk (fun a : ℕ × (Header Pt × LibsignalMsgPublicPart) => a.2.2.shortB) B)
    (hdec : GuardedOTDecShort B) :
    𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true N B].boolDist
      𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) false N B] ≤
    (∑ k ∈ Finset.range N,
      (2 * (lSaltPRF32 C.F).prfAdvantage
          (lSaltRed C codec ℓ encT idOf (slotSaltRed C codec ℓ encT idOf N k B)) +
        (lWire C codec ℓ).wireOtccaAdvantage
          (lWireRed C codec ℓ encT idOf 0 (slotWireRed C codec ℓ encT idOf k B)))) +
      (qd : ℝ≥0∞) * macForgeryProb C.F := by
  have hℓ_rust : ℓ + 16 < rustLenBound := by unfold rustLenBound; omega
  rw [Measure.boolDist_comm]
  have h2 := SaltHop.multiOtBranch_false_boolDist_multiSalt_false C codec ℓ encT idOf N B hoff
  have h3 := SaltHop.multiSalt_false_boolDist_multiSaltNF_false C codec hfit ℓ hℓ encT idOf B hqd
    hshort hdec
  have h4 := multiSaltNF_false_boolDist_multiOtBranch_true C codec hrt ℓ hℓ_rust encT hinj hdum
    idOf hN B hoff hcls hshort
  have htri1 := Measure.boolDist_triangle
    𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) false N B]
    𝒟[Prod.fst <$> (simulateQ (FSAEAD.Thm5.slotLift (slotSaltImpl C codec ℓ encT idOf false)) B).run
      (fun _ => {})]
    𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true N B]
  have htri2 := Measure.boolDist_triangle
    𝒟[Prod.fst <$> (simulateQ (FSAEAD.Thm5.slotLift (slotSaltImpl C codec ℓ encT idOf false)) B).run
      (fun _ => {})]
    𝒟[Prod.fst <$> (simulateQ (FSAEAD.Thm5.slotLift (slotSaltImplNF C codec ℓ encT idOf false)) B).run
      (fun _ => {})]
    𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true N B]
  refine (htri1.trans (add_le_add h2 (htri2.trans (add_le_add h3 h4)))).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib]
  ring

theorem lFS_full_bound_short_proof [DecidableEq Pt] (C : Crypto) (hD : ∀ k x, C.D k (C.E k x) = x)
    (codec : SignalMessageProtoCodec) (hrt : SignalRoundTripShort codec)
    (hfit : SignalEncodeFits32 codec) (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16)
    (encT : Pt → PublicKey) (hinj : Function.Injective encT) (hdum : ∀ T, encT T ≠ dummyKey)
    (idOf : Party → IdentityKey) (maxSkip : ℕ) (hms : maxSkip ≤ 25000)
    (A : FSAEAD.RatchetAdversary (BitVec 256) (BitVec 256) (Header Pt) (LibsignalMsgPublicPart × Plain ℓ)
      LibsignalCiphertextWithSalt32) (q qd : ℕ)
    (hq : FSAEAD.MakesAtMostQueries A q)
    (hqd : FSAEAD.MakesAtMostDecQueries A qd)
    (hq32 : q + 25002 < 2 ^ 32)
    (heq : FSAEAD.EqualPubChallenges A)
    (hcls : FSAEAD.AllQueriesInOneADClass (fun h : Header Pt => h.1) A)
    (hshort : FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) A)
    (hinj_short : GuardedFSInjectShort A) :
    let A' := FSAEAD.pubRed
      (fun c : ℕ × LibsignalCiphertextWithSalt32 => lPubOf codec c.2) A
    let B (la : Bool) := FSAEAD.Thm5.multiSlotOtccaReduction (lIdeal C codec ℓ encT)
      (lAeadR C codec ℓ encT idOf) (lChainPRG C.F) maxSkip
      (if la then q + (maxSkip + 1) else q) la A'
    FSAEAD.advantage (lFS C codec ℓ encT idOf maxSkip) A ≤
      2 * ∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip q),
        ((lChainPRG C.F (FSAEAD.Thm5.slotToHybridHopIndex q j / 2)).prgAdvantage
            (FSAEAD.Thm5.cumulativeChainPrgReduction (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
              (lChainPRG C.F) maxSkip (FSAEAD.Thm5.slotToHybridHopIndex q j) A') +
          (2 * (lSaltPRF32 C.F).prfAdvantage
              (lSaltRed C codec ℓ encT idOf
                (slotSaltRed C codec ℓ encT idOf
                  (if FSAEAD.Thm5.isLookaheadHop (FSAEAD.Thm5.slotToHybridHopIndex q j) then q + (maxSkip + 1) else q)
                  (FSAEAD.Thm5.slotToHybridHopIndex q j / 2)
                  (B (FSAEAD.Thm5.isLookaheadHop (FSAEAD.Thm5.slotToHybridHopIndex q j))))) +
            (lWire C codec ℓ).wireOtccaAdvantage
              (lWireRed C codec ℓ encT idOf 0
                (slotWireRed C codec ℓ encT idOf (FSAEAD.Thm5.slotToHybridHopIndex q j / 2)
                  (B (FSAEAD.Thm5.isLookaheadHop (FSAEAD.Thm5.slotToHybridHopIndex q j))))))) +
      4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
  intro A' B
  have hℓ_rust : ℓ + 16 < rustLenBound := by unfold rustLenBound; omega
  obtain ⟨hq', -, hA', hadv⟩ := ProstPubToAD.pubMsg_red_on (lAead C codec ℓ encT idOf) (lPubOf codec)
    LibsignalMsgPublicPart.shortB (ProstMsgAeadCorrect.lPubOf_enc_short_proof C codec hrt ℓ hℓ_rust encT idOf) (lChainPRG C.F)
    maxSkip (fun h : Header Pt => h.1) A q hq heq hcls hshort
  have hinj_A' : GuardedFSInjectShort A' := pubRed_guardedFSInjectShort _ A hinj_short
  have hqd' : FSAEAD.MakesAtMostDecQueries A' qd :=
    IndexRestrictions.pubRed_makesAtMostDecQueries _ A hqd
  have hcls' : FSAEAD.AllQueriesInOneADClass (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) A' :=
    IndexRestrictions.pubRed_adClassConst (fun h : Header Pt => h.1) _ A hcls
  have hthm5 := hadv.trans (FSAEAD.Thm5.theorem5With_on_multi (lAeadR C codec ℓ encT idOf)
    (lChainPRG C.F) maxSkip (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB)
    (ProstMsgAeadCorrect.lAeadR_correctOn_short_proof C hD codec hrt ℓ hℓ_rust encT idOf)
    (lIdeal C codec ℓ encT) A' q hq' hA')
  have hchain : ∀ (la : Bool),
      let N := if la then q + (maxSkip + 1) else q
      𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true N
          (B la)].boolDist
        𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) false N
          (B la)] ≤
      (∑ k ∈ Finset.range N,
        (2 * (lSaltPRF32 C.F).prfAdvantage
            (lSaltRed C codec ℓ encT idOf (slotSaltRed C codec ℓ encT idOf N k (B la))) +
          (lWire C codec ℓ).wireOtccaAdvantage
            (lWireRed C codec ℓ encT idOf 0 (slotWireRed C codec ℓ encT idOf k (B la))))) +
        (qd : ℝ≥0∞) * macForgeryProb C.F := by
    intro la N
    have hN : N ≤ 2 ^ 32 := by cases la <;> dsimp [N] <;> omega
    exact multiOtBranch_boolDist_le_short C codec hrt hfit ℓ hℓ encT hinj hdum idOf hN (B la)
      (FSAEAD.Thm5.multiRedWith_offRange _ _ _ _ N la A')
      (multiRedWith_makesAtMostDecQueries _ _ _ _ N la A' hqd')
      (multiRedWith_otADClassConst (fun ap : Header Pt × LibsignalMsgPublicPart => ap.1.1) _ _ _ _ N la A' hcls')
      (multiRedWith_otEncADsOk (fun ap : Header Pt × LibsignalMsgPublicPart => ap.2.shortB) _ _ _ _ N la A' hA')
      (multiRedWith_guardedOTDecShort C codec hfit ℓ hℓ encT idOf maxSkip N la A' hA' hinj_A')
  have hF := hchain false
  have hT := hchain true
  simp only [Bool.false_eq_true, ↓reduceIte] at hF hT
  set fP : ℕ → ℝ≥0∞ := fun m =>
    (lChainPRG C.F (m / 2)).prgAdvantage
      (FSAEAD.Thm5.cumulativeChainPrgReduction (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf)
        (lChainPRG C.F) maxSkip m A')
  set fSW : ℕ → ℝ≥0∞ := fun m =>
    2 * (lSaltPRF32 C.F).prfAdvantage
        (lSaltRed C codec ℓ encT idOf
          (slotSaltRed C codec ℓ encT idOf
            (if FSAEAD.Thm5.isLookaheadHop m then q + (maxSkip + 1) else q)
            (m / 2) (B (FSAEAD.Thm5.isLookaheadHop m)))) +
      (lWire C codec ℓ).wireOtccaAdvantage
        (lWireRed C codec ℓ encT idOf 0
          (slotWireRed C codec ℓ encT idOf (m / 2) (B (FSAEAD.Thm5.isLookaheadHop m))))
  have hsumF :
      ∑ k ∈ Finset.range q,
        (2 * (lSaltPRF32 C.F).prfAdvantage
            (lSaltRed C codec ℓ encT idOf (slotSaltRed C codec ℓ encT idOf q k (B false))) +
          (lWire C codec ℓ).wireOtccaAdvantage
            (lWireRed C codec ℓ encT idOf 0 (slotWireRed C codec ℓ encT idOf k (B false)))) =
      ∑ k ∈ Finset.range q, fSW (2 * k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdiv : (2 * k) / 2 = k := by omega
    have hla : FSAEAD.Thm5.isLookaheadHop (2 * k) = false := by simp [FSAEAD.Thm5.isLookaheadHop]
    dsimp only [fSW]
    rw [hdiv, hla]
    simp
  have hsumT :
      ∑ k ∈ Finset.range (q + (maxSkip + 1)),
        (2 * (lSaltPRF32 C.F).prfAdvantage
            (lSaltRed C codec ℓ encT idOf
              (slotSaltRed C codec ℓ encT idOf (q + (maxSkip + 1)) k (B true))) +
          (lWire C codec ℓ).wireOtccaAdvantage
            (lWireRed C codec ℓ encT idOf 0 (slotWireRed C codec ℓ encT idOf k (B true)))) =
      ∑ k ∈ Finset.range (q + (maxSkip + 1)), fSW (2 * k + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hdiv : (2 * k + 1) / 2 = k := by omega
    have hla : FSAEAD.Thm5.isLookaheadHop (2 * k + 1) = true := by simp [FSAEAD.Thm5.isLookaheadHop, Nat.add_mod]
    dsimp only [fSW]
    rw [hdiv, hla]
    simp
  rw [hsumF] at hF
  rw [hsumT] at hT
  have hFT :
      2 * (𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true q
            (B false)].boolDist
          𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) false q
            (B false)] +
        𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) true
            (q + (maxSkip + 1)) (B true)].boolDist
          𝒟[FSAEAD.Thm5.multiOtBranch (lIdeal C codec ℓ encT) (lAeadR C codec ℓ encT idOf) false
            (q + (maxSkip + 1)) (B true)]) ≤
      2 * (((∑ k ∈ Finset.range q, fSW (2 * k)) + (qd : ℝ≥0∞) * macForgeryProb C.F) +
        ((∑ k ∈ Finset.range (q + (maxSkip + 1)), fSW (2 * k + 1)) +
          (qd : ℝ≥0∞) * macForgeryProb C.F)) := by
    gcongr
  refine (hthm5.trans (add_le_add le_rfl hFT)).trans (le_of_eq ?_)
  have hsplit := FSAEAD.Thm5.sum_range_hopIdx fSW maxSkip q
  calc 2 * (∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip q), fP (FSAEAD.Thm5.slotToHybridHopIndex q j)) +
        2 * (((∑ k ∈ Finset.range q, fSW (2 * k)) + (qd : ℝ≥0∞) * macForgeryProb C.F) +
          ((∑ k ∈ Finset.range (q + (maxSkip + 1)), fSW (2 * k + 1)) +
            (qd : ℝ≥0∞) * macForgeryProb C.F))
      = 2 * (∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip q), fP (FSAEAD.Thm5.slotToHybridHopIndex q j)) +
        2 * ((∑ k ∈ Finset.range q, fSW (2 * k) +
            ∑ k ∈ Finset.range (q + (maxSkip + 1)), fSW (2 * k + 1)) +
          2 * ((qd : ℝ≥0∞) * macForgeryProb C.F)) := by ring
    _ = 2 * (∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip q), fP (FSAEAD.Thm5.slotToHybridHopIndex q j)) +
        2 * ((∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip q), fSW (FSAEAD.Thm5.slotToHybridHopIndex q j)) +
          2 * ((qd : ℝ≥0∞) * macForgeryProb C.F)) := by rw [hsplit]
    _ = 2 * (∑ j ∈ Finset.range (FSAEAD.Thm5.slotCount maxSkip q),
          (fP (FSAEAD.Thm5.slotToHybridHopIndex q j) + fSW (FSAEAD.Thm5.slotToHybridHopIndex q j))) +
        4 * ((qd : ℝ≥0∞) * macForgeryProb C.F) := by
      rw [Finset.sum_add_distrib
        (f := fun j => fP (FSAEAD.Thm5.slotToHybridHopIndex q j))
        (g := fun j => fSW (FSAEAD.Thm5.slotToHybridHopIndex q j))]
      ring

end CryptoGames.LibsignalSM.Proofs.ProstFSAEADBound

