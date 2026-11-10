/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
public import LibsignalBinary.Proofs.PeakBudget.GateM2rGSite3Eq
public import LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs
public import LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux
public import LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux
public import LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
public import LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
public import LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyCmkSlot
public import LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureUntrustedPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# `clearPending` Length Bounds and `TopStateTight`-Guarded `tryDecrypt` Bridges (`W4`)

Establishes protobuf `clearPending` serialized-length monotonicity (`≤ 2 ^ 21` under
`loadRel`), `VerNeTightTopRawEnv → VerNeTightTopEnv` upgrades, and `TopStateTight`
collapse lemmas for `w4s2_TryDecryptTopStateGuardedEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkStep2

open CryptoGames.LibsignalSession
  (ChainKey Crypto MessageKeyGenerator Mut RatchetState SessionState ShaCompress TripleRatchet)
open CryptoGames.LibsignalSessionApi (Session SessionRecord)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (clearPending)
open CryptoVerification.E2E.Record
  (encSession encodeRecord lenField msgField)
open CryptoVerification.LibsignalProtoCodec (encodeVarint encodeVarintAux)
open CryptoVerification.LibsignalPublicApi.StoreKit (FsFiles)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalTripleRatchet (TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost coinsOf uuidTryParse)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SignalSession (CliHooks)
open CryptoVerification.SignalSession.Cli (StoresGhost)
open CryptoVerification.SignalSession.Cli.RunProofs.Poll (cliKitStk cliPollSessKitPlaced)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs SeqEnv rustAllocEvents)
open LibsignalBinary.Heap.SpecBudget (FmtWriteEnv FormatInnerEnv)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (CmkLoopAdvanceEvs)
open LibsignalBinary.Proofs.PeakBudget.CliRealBinaryKitEnvs (W4BinaryArchiveDirectEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
  (cliIo_rd_ok_length_le_sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.DecPkD2cSlotOkLinked
  (TryDecryptCliEnvOfPure tryDecryptCmkSeg4Env tryDecryptEnvArgsToGhost)
open LibsignalBinary.Proofs.PeakBudget.GateM2rGStatesRecvTwins
  (m2rg_TryDecryptCliLinkedEnvOf' m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed')
open LibsignalBinary.Proofs.PeakBudget.RealCliDecPkGuardedDefs (cliDecPkCanonSlotEnvExact)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.SpqrStatesRecvPeakSpecRepaired (StatesRecvProtoEnv')
open LibsignalBinary.Proofs.PeakBudget.SpqrTrialDomainLiftAux (TopStateTight)
open LibsignalBinary.Proofs.PeakBudget.TryDecryptCliLinkedOf
  (SpqrRecvC07C09aBytesEnvOf TryDecryptCliLinkedEnvOf spqrRecvC07C09aBytesEnvOf_nonempty
   tryDecryptCliLinkedEnvOf_eq_pure)
open LibsignalBinary.Proofs.PeakBudget.W4InitBobPeak (W4BoundedEvs)
open LibsignalBinary.Proofs.PeakBudget.W4PathCVerNeWideDefs
  (VerNeSessionCancelEnv VerNeSessionCancelRawEnv VerNeTightTopEnv VerNeTightTopRawEnv)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudget (deserCancelFineMaxReq)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.Stage2OverInstPlacedBudget
  (PromoteOverArchiveCanonSessEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.AesDecryptBudget (s8Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ApplyRatchetBudget (s9Env)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepBudgetCore (s3DefaultEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs (PqRecvEnv)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.RootBudgetAux
  (FromS2GenEnv FromS3GenEnv FromS4GenEnv FromS5GenEnv s1InitTrGhost stdAesOpt)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudget (s7Env)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)

/-! ## `cliDecPkCanonSlotEnvExact` Definitional Alignment -/

/-- Definitional alignment of `cliDecPkCanonSlotEnvExact` with `m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'`. -/
theorem w4s2_cliDecPkCanonSlotEnvExact_eq [LibsignalPlacement] :
    cliDecPkCanonSlotEnvExact =
      m2rg_realCliDecPkBinaryWideSlotEnvCmkVerNeGuardedFixed'
        (fun _ K => StatesRecvProtoEnv' K) :=
  rfl

/-! ## `clearPending` Serialized-Length Monotonicity and `2 MiB` `VerNe` Bounds -/

private theorem w4s2_encSession_clearPending_le (s : Session (List (BitVec 8))) :
    (encSession (clearPending s)).length ≤ (encSession s).length := by
  unfold encSession clearPending
  dsimp only [Option.map, msgField]
  simp only [List.length_append, List.length_nil]
  omega

private theorem w4s2_lenField_length_ge (tag : Nat) (b : List (BitVec 8)) :
    b.length ≤ (lenField tag b).length := by
  unfold lenField
  simp only [List.length_append]
  omega

/-- Clearing pending pre-key fields does not exceed the serialized outer `SessionRecord` byte length when `r.currentSession = some s_old`. -/
theorem w4s2_encSession_clearPending_le_encodeRecord
    (r : SessionRecord (List (BitVec 8))) (s_old : Session (List (BitVec 8)))
    (hcur : r.currentSession = some s_old) :
    (encSession (clearPending s_old)).length ≤ (encodeRecord r).length := by
  have h1 := w4s2_encSession_clearPending_le s_old
  have h2 : (encSession s_old).length ≤ (encodeRecord r).length := by
    unfold encodeRecord
    rw [hcur]
    dsimp only [Option.map, msgField]
    exact w4s2_lenField_length_ge 1 (encSession s_old)
  exact Nat.le_trans h1 h2

private theorem w4s2_encodeVarintAux_length_mono :
    ∀ (k : Nat) {v₁ v₂ : BitVec 64}, v₁.toNat ≤ v₂.toNat →
      (encodeVarintAux k v₁).length ≤ (encodeVarintAux k v₂).length
  | 0, _, _, _ => by simp [encodeVarintAux]
  | k + 1, v₁, v₂, hle => by
    unfold encodeVarintAux
    split
    · split <;> simp
    · rename_i h₁
      split
      · rename_i h₂
        omega
      · simp only [List.length_cons]
        have hsh : (v₁ >>> 7).toNat ≤ (v₂ >>> 7).toNat := by
          rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
            Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
          exact Nat.div_le_div_right hle
        have ih := w4s2_encodeVarintAux_length_mono k hsh
        omega

/-- LEB128 `encodeVarint` byte-length monotonicity below `2 ^ 64`. -/
theorem w4s2_encodeVarint_ofNat_length_mono {a b : Nat}
    (hle : a ≤ b) (hlt : b < 2 ^ 64) :
    (encodeVarint (BitVec.ofNat 64 a)).length ≤ (encodeVarint (BitVec.ofNat 64 b)).length := by
  unfold encodeVarint
  apply w4s2_encodeVarintAux_length_mono 10
  simp only [BitVec.toNat_ofNat]
  omega

private theorem w4s2_lenField_length_mono {tag : Nat} {b₁ b₂ : List (BitVec 8)}
    (hle : b₁.length ≤ b₂.length) (hlt : b₂.length < 2 ^ 64) :
    (lenField tag b₁).length ≤ (lenField tag b₂).length := by
  unfold lenField
  simp only [List.length_append]
  have hv := w4s2_encodeVarint_ofNat_length_mono hle hlt
  omega

/-- Record-level `encodeRecord` length monotonicity under `clearPending` below `2 ^ 64`. -/
theorem w4s2_encodeRecord_clearPending_le_encodeRecord
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hcur : r.currentSession = some s_old)
    (hlt : (encodeRecord r).length < 2 ^ 64) :
    (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ (encodeRecord r).length := by
  have h1 := w4s2_encSession_clearPending_le s_old
  have h2 : (encSession s_old).length ≤ (encodeRecord r).length := by
    unfold encodeRecord
    rw [hcur]
    dsimp only [Option.map, msgField]
    exact w4s2_lenField_length_ge 1 (encSession s_old)
  have hb_lt : (encSession s_old).length < 2 ^ 64 := Nat.lt_of_le_of_lt h2 hlt
  unfold encodeRecord
  rw [hcur]
  dsimp only [Option.map, msgField]
  exact w4s2_lenField_length_mono h1 hb_lt

private theorem w4s2_seqEnv_mono {A₁ A₂ B₁ B₂ : List AllocEvent → Prop}
    (hA : ∀ e, A₁ e → A₂ e) (hB : ∀ e, B₁ e → B₂ e)
    {evs : List AllocEvent} (h : SeqEnv A₁ B₁ evs) :
    SeqEnv A₂ B₂ evs := by
  rcases h with h1 | ⟨evs₁, evs₂, rfl, h1, h2⟩
  · exact Or.inl (hA evs h1)
  · exact Or.inr ⟨evs₁, evs₂, rfl, hA evs₁ h1, hB evs₂ h2⟩

private theorem w4s2_w4BoundedEvs_alloc96 :
    W4BoundedEvs 1 192 (rustAllocEvents 96 8) := by
  have heq : rustAllocEvents 96 8 = [.alloc 96] := by
    unfold rustAllocEvents
    decide
  rw [heq]
  refine ⟨by decide, ?_⟩
  intro ev hev
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, by decide⟩

private theorem w4s2_w4BoundedEvs_nil :
    W4BoundedEvs 1 192 [] := by
  refine ⟨by decide, ?_⟩
  intro ev hev
  cases hev

/-- When `r.currentSession = some s_old`, `PromoteOverArchiveCanonSessEnv s_old` embeds into `W4BinaryArchiveDirectEnv (encodeRecord r).length`. -/
theorem w4s2_promoteOverArchive_sub_w4ArchiveDirect
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    {evs : List AllocEvent}
    (hcur : r.currentSession = some s_old)
    (hprom : PromoteOverArchiveCanonSessEnv s_old evs) :
    W4BinaryArchiveDirectEnv (encodeRecord r).length evs := by
  have hn : (encSession (clearPending s_old)).length ≤ (encodeRecord r).length :=
    w4s2_encSession_clearPending_le_encodeRecord r s_old hcur
  unfold PromoteOverArchiveCanonSessEnv at hprom
  unfold W4BinaryArchiveDirectEnv
  rcases hprom with h96 | hnil
  · refine w4s2_seqEnv_mono (fun _ h => h) ?_ h96
    intro e₁ he₁
    refine w4s2_seqEnv_mono
      (fun e he => ⟨(encSession (clearPending s_old)).length, hn, he⟩) ?_ he₁
    intro e₂ he₂
    exact w4s2_seqEnv_mono
      (fun e he => he ▸ w4s2_w4BoundedEvs_alloc96) (fun _ h => h) he₂
  · refine w4s2_seqEnv_mono (fun _ h => h) ?_ hnil
    intro e₁ he₁
    refine w4s2_seqEnv_mono
      (fun e he => ⟨(encSession (clearPending s_old)).length, hn, he⟩) ?_ he₁
    intro e₂ he₂
    exact w4s2_seqEnv_mono
      (fun e he => he ▸ w4s2_w4BoundedEvs_nil) (fun _ h => h) he₂

/-- Scope-polymorphic `≤ 2 ^ 21` (`sessionCapBytes`) bound on `(encodeRecord r).length` from `loadRel`. -/
theorem w4s2_loadRel_encodeRecord_le_sessionCap_of_loadRel [LibsignalPlacement]
    {A : RustAlloc} {F : FsFiles} {scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {B : RunBudgets}
    {r : SessionRecord (List (BitVec 8))}
    (hload : (cliPollSessKitPlaced A F scope peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r))) :
    (encodeRecord r).length ≤ sessionCapBytes := by
  obtain ⟨bs, hget, hans⟩ := hload
  have hbs : bs.length ≤ sessionCapBytes :=
    cliIo_rd_ok_length_le_sessionCapBytes F _ bs hget
  cases bs with
  | nil => cases hans
  | cons b₀ bs' =>
    obtain ⟨r', hr', henc, _⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    rw [henc]
    exact hbs

/-- Scope-polymorphic `≤ 2 ^ 21` bound on `(encodeRecord ⟨some (clearPending s_old)⟩).length` from `loadRel`. -/
theorem w4s2_encodeRecord_clearPending_le_cap_of_loadRel [LibsignalPlacement]
    {A : RustAlloc} {F : FsFiles} {scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {B : RunBudgets}
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    (hload : (cliPollSessKitPlaced A F scope peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old) :
    (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21 := by
  have hr_cap : (encodeRecord r).length ≤ sessionCapBytes :=
    w4s2_loadRel_encodeRecord_le_sessionCap_of_loadRel hload
  have hcap_eq : sessionCapBytes = 2 ^ 21 := rfl
  have hr_lt : (encodeRecord r).length < 2 ^ 64 := by
    rw [hcap_eq] at hr_cap
    omega
  have hmono : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ (encodeRecord r).length :=
    w4s2_encodeRecord_clearPending_le_encodeRecord hcur hr_lt
  rw [hcap_eq] at hr_cap
  exact Nat.le_trans hmono hr_cap

/-- Upgrades `VerNeSessionCancelRawEnv` to `VerNeSessionCancelEnv` when `(encodeRecord ⟨some s₀⟩).length ≤ 2 ^ 21`. -/
theorem w4s2_verNeSessionCancelRaw_to_tight
    {s₀ : Session (List (BitVec 8))} {evs : List AllocEvent}
    (hcap : (encodeRecord ⟨some s₀⟩).length ≤ 2 ^ 21)
    (hraw : VerNeSessionCancelRawEnv (encSession s₀) evs) :
    VerNeSessionCancelEnv (encSession s₀) evs := by
  rcases hraw with ⟨s', henc, hdes⟩
  have hrec : encodeRecord ⟨some s'⟩ = encodeRecord ⟨some s₀⟩ := by
    unfold encodeRecord
    dsimp only [Option.map]
    rw [← henc]
  have hreq_eq : deserCancelFineMaxReq = 2 ^ 21 := rfl
  have hlen' : (encodeRecord ⟨some s'⟩).length ≤ deserCancelFineMaxReq := by
    rw [hrec, hreq_eq]
    exact hcap
  exact ⟨s', henc, hlen', hdes⟩

/-- Upgrades `VerNeTightTopRawEnv` to `VerNeTightTopEnv` when `(encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21`. -/
theorem w4s2_verNeRaw_to_verNeTight_of_cap
    {s_old : Session (List (BitVec 8))} {evs : List AllocEvent}
    (hcap : (encodeRecord ⟨some (clearPending s_old)⟩).length ≤ 2 ^ 21)
    (hraw : VerNeTightTopRawEnv (encSession (clearPending s_old)) evs) :
    VerNeTightTopEnv (encSession (clearPending s_old)) evs := by
  refine w4s2_seqEnv_mono (fun _ h => h) ?_ hraw
  intro e₁ he₁
  refine w4s2_seqEnv_mono ?_ (fun _ h => h) he₁
  intro e₂ he₂
  exact w4s2_seqEnv_mono
    (fun _ h => w4s2_verNeSessionCancelRaw_to_tight hcap h) (fun _ h => h) he₂

/-- Upgrades `VerNeTightTopRawEnv` to `VerNeTightTopEnv` directly from `loadRel`. -/
theorem w4s2_verNeRaw_to_verNeTight_of_loadRel [LibsignalPlacement]
    {A : RustAlloc} {F : FsFiles} {scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {B : RunBudgets}
    {r : SessionRecord (List (BitVec 8))} {s_old : Session (List (BitVec 8))}
    {evs : List AllocEvent}
    (hload : (cliPollSessKitPlaced A F scope peer (cliKitStk B)).loadRel
      StoresGhost.opened.sessions peer.val (.ok (some r)))
    (hcur : r.currentSession = some s_old)
    (hraw : VerNeTightTopRawEnv (encSession (clearPending s_old)) evs) :
    VerNeTightTopEnv (encSession (clearPending s_old)) evs :=
  w4s2_verNeRaw_to_verNeTight_of_cap
    (w4s2_encodeRecord_clearPending_le_cap_of_loadRel hload hcur) hraw

/-! ## `TopStateTight`-Guarded Block-507 `tryDecrypt` Envelope Collapse -/

theorem w4s2_tryDecryptCliLinkedEnvOf_eq_m2rg (maxOps : Nat) (C : Crypto) (K : MlKem) :
    TryDecryptCliLinkedEnvOf maxOps C K =
      m2rg_TryDecryptCliLinkedEnvOf' CmkLoopAdvanceEvs maxOps C K (StatesRecvProtoEnv' K) :=
  rfl

/-- `TopStateTight`-guarded `spqr::recv` byte-slice envelope at `maxOps = 109`. -/
def w4s2_SpqrRecvTopStateGuardedBytesEnv (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  TopStateTight F K stBs → SpqrRecvC07C09aBytesEnvOf 109 F K stBs msgBs evs

theorem w4s2_spqrRecvTopStateGuardedBytesEnv_nonempty (F : ShaCompress) (K : MlKem)
    (stBs msgBs : List (BitVec 8)) :
    ∃ evs, w4s2_SpqrRecvTopStateGuardedBytesEnv F K stBs msgBs evs :=
  let ⟨evs, hevs⟩ := spqrRecvC07C09aBytesEnvOf_nonempty 109 F K stBs msgBs
  ⟨evs, fun _ => hevs⟩

/-- `TryDecryptCliEnvOfPure` instantiated at `w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K`. -/
noncomputable def w4s2_TryDecryptTopStateGuardedEnv (W : CliHooks) :
    TryDecryptEnvArgs → List AllocEvent → Prop :=
  TryDecryptCliEnvOfPure W.C (spqrV1 W.C.F W.Q.K) FmtWriteEnv
    (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv

private theorem w4s2_fromSessionState_ok_pqrState {PQ : Type} [Inhabited PQ]
    {s s1 : SessionState PQ} {tr0 : TripleRatchet PQ}
    (h : Mut.exec TripleRatchet.fromSessionState s = (.ok tr0, s1)) :
    tr0.pqrState = s.pqRatchetState := by
  unfold Mut.exec TripleRatchet.fromSessionState SessionState.takeRatchetState
    SessionState.takePqRatchetState at h
  rcases s with ⟨_, _, _ | rem, _, _, _, _, _, _⟩
  · cases h
  · cases h; rfl

private theorem w4s2_pqRecvEnv_topStateGuarded_eq (W : CliHooks)
    (x : TryDecryptGhost) (tr : TripleRatchet (List (BitVec 8)))
    (hTop : TopStateTight W.C.F W.Q.K tr.pqrState) :
    PqRecvEnv (spqrV1 W.C.F W.Q.K) (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K)
        FormatInnerEnv x tr =
      PqRecvEnv (spqrV1 W.C.F W.Q.K) (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K)
        FormatInnerEnv x tr := by
  have hrecv :
      w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K tr.pqrState x.msg.pqRatchet =
        SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K tr.pqrState x.msg.pqRatchet := by
    funext evs
    exact propext ⟨fun h => h hTop, fun h _ => h⟩
  unfold PqRecvEnv
  rw [hrecv]

/-- Under `TopStateTight`, `w4s2_TryDecryptTopStateGuardedEnv W a` equals `TryDecryptCliLinkedEnvOf 109 W.C W.Q.K a`. -/
theorem w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top (W : CliHooks)
    (a : TryDecryptEnvArgs)
    (hTop : TopStateTight W.C.F W.Q.K a.st.pqRatchetState) :
    w4s2_TryDecryptTopStateGuardedEnv W a = TryDecryptCliLinkedEnvOf 109 W.C W.Q.K a := by
  rw [tryDecryptCliLinkedEnvOf_eq_pure 109 W.C W.Q.K]
  unfold w4s2_TryDecryptTopStateGuardedEnv TryDecryptCliEnvOfPure
  cases hfrom : Mut.exec TripleRatchet.fromSessionState a.st with
  | mk res st1 =>
    cases res with
    | error _ => rfl
    | ok tr0 =>
      dsimp only
      apply congrArg (SeqEnv FreeOnlyEvs)
      let x := tryDecryptEnvArgsToGhost a
      let S := spqrV1 W.C.F W.Q.K
      let s4Env := tryDecryptCmkSeg4Env FmtWriteEnv
      have hTop0 : TopStateTight W.C.F W.Q.K tr0.pqrState :=
        (w4s2_fromSessionState_ok_pqrState hfrom).symm ▸ hTop
      have hs5g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
          (mkg : MessageKeyGenerator),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg =
            FromS5GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 mkg := by
        intro trG tr mkg hT
        unfold FromS5GenEnv
        rw [w4s2_pqRecvEnv_topStateGuarded_eq W x tr hT]
      have hs4g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (ck : ChainKey),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck =
            FromS4GenEnv W.C uuidTryParse S (stdAesOpt W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 ck := by
        intro trG tr ck hT
        unfold FromS4GenEnv
        cases Mut.exec
            (RatchetState.consumeMessageKey W.C.F x.msg.senderRatchetKey ck x.msg.counter x.msgType)
            tr.ratchet with
        | mk r4 r2 =>
          cases r4 with
          | error _ => rfl
          | ok mkg =>
            dsimp only
            exact congrArg (SeqEnv (s4Env x trG tr ck))
              (hs5g trG { tr with ratchet := r2 } mkg hT)
      have hs3g : ∀ (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))),
          TopStateTight W.C.F W.Q.K tr.pqrState →
          FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (w4s2_SpqrRecvTopStateGuardedBytesEnv W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 =
            FromS3GenEnv W.C uuidTryParse S (stdAesOpt W.C)
              (s3DefaultEnv W.C) s4Env
              (PqRecvEnv S (SpqrRecvC07C09aBytesEnvOf 109 W.C.F W.Q.K) FormatInnerEnv)
              s6FreeOnlyEnv (s7Env W.C.F uuidTryParse) s8Env s9Env x trG tr st1 := by
        intro trG tr hT
        unfold FromS3GenEnv
        cases Mut.exec (RatchetState.dhRatchetStep W.C x.msg.senderRatchetKey (coinsOf x.rest))
            tr.ratchet with
        | mk r3 r1 =>
          cases r3 with
          | error _ => rfl
          | ok ck =>
            dsimp only
            exact congrArg (SeqEnv (s3DefaultEnv W.C x trG tr))
              (hs4g _ { tr with ratchet := r1 } ck hT)
      unfold FromS2GenEnv
      cases tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error _ => rfl
      | ok cko =>
        cases cko with
        | some ck =>
          dsimp only
          exact hs4g (s1InitTrGhost a.G) tr0 ck hTop0
        | none =>
          dsimp only
          exact hs3g (s1InitTrGhost a.G) tr0 hTop0

theorem w4s2_tryDecryptTopStateGuardedEnv_eq_m2rg_of_top (W : CliHooks)
    (a : TryDecryptEnvArgs)
    (hTop : TopStateTight W.C.F W.Q.K a.st.pqRatchetState) :
    w4s2_TryDecryptTopStateGuardedEnv W a =
      m2rg_TryDecryptCliLinkedEnvOf' CmkLoopAdvanceEvs 109 W.C W.Q.K
        (StatesRecvProtoEnv' W.Q.K) a :=
  (w4s2_tryDecryptTopStateGuardedEnv_eq_linked_of_top W a hTop).trans
    (congrFun (w4s2_tryDecryptCliLinkedEnvOf_eq_m2rg 109 W.C W.Q.K) a)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W4DecPkStep2
