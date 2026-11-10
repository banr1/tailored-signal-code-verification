/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperFS
public import Computational.Proofs.HeadlineV1.DeliverForgePaperShiftedReds
public import Computational.Proofs.ReductionDsl.SM.DeliverForgePaperPRNG
import ProofLib.BV.WidthNorm
import VCVio.EvalDist.Monad.Basic
import Computational.Proofs.ReductionDsl.Notation

/-!
# Costed FS-AEAD Shifted Paper Reductions and Cost Dominance

Defines the costed FS-AEAD shifted paper reductions and proves their advantage bridges and
paper-vs-non-paper cost dominance bounds.
-/

@[expose] public section

set_option autoImplicit false
open scoped BigOperators ENNReal Computational.Proofs.ReductionDsl.Notation
open ReductionDsl ReductionDsl.Comp OracleSpec OracleComp
open CryptoGames CryptoGames.CKA CryptoGames.PRFPRNG CryptoGames.FSAEAD CryptoGames.SM
open CryptoGames.SM.Engine CryptoGames.SM.Engine.RedPRNG CryptoGames.SM.Construction
open CryptoGames.SM.Construction.DeliverForge
namespace CryptoGames.SM.Construction
variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}
section HooksFSCDFShiftedPaper

variable {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S" => prngSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II" =>
  fsaeadHeaderAdIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "esTyFS" => fsEsTy KC Γ CCoins T I KR RSt K SS RS M E

def runFSDFShiftedPaper [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E]
    [Inhabited E] [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (l Δcka qep tStar : ℕ) (mo mo' : Mode)
    (j : ℕ) (b : Bool) (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × EState (VP Γ T RSt (Option SS) (Option RS)) M (Header T × E)
        (FSState T RSt K I SS RS E))) :=
  DeliverForge.engRunDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep
    fs.maxSkip tStar mo'.cfg mo'.policy (initFS cka prng fs lam mo j) {} b A

theorem runFSDFShiftedPaper_eq_bind_initFSRaw
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (l Δcka qep tStar : ℕ) (mo mo' : Mode)
    (j : ℕ) (b : Bool) (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) :
    runFSDFShiftedPaper b1 cka prng fs lam l Δcka qep tStar mo mo' j b A =
      (do
        let es₀ ← initFSRaw cka prng fs lam mo j b
        let res ← (simulateQ (DeliverForge.implEDFShiftedPaperGen b1 l
          (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip tStar mo'.cfg mo'.policy)
          A).run es₀
        pure (some res)) := by
  unfold runFSDFShiftedPaper DeliverForge.engRunDFShiftedPaperGen initFS initFSRaw
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  refine bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun ⟨⟨_, _, _⟩, _⟩ => bind_congr fun ⟨_, _⟩ => rfl

/-- Costed shifted paper FS-AEAD reduction parameterized by `authH : Bool`. -/
def redFSAuthDFShiftedPaperGenProg (L B Δcka qep maxSkip j l tStar : ℕ) (authH : Bool) :
    CostedReduction OO II (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool where
  σ := esTyFS
  init := rdsl [_] do
    es ← initFSEStateC L (raw ⟨authH, some (l - 1), tStar⟩) j false
    return ((), es)
  handle := rdsl [st, q] do
    implECDFShiftedPaperGen (raw (!authH))
      (raw (hooksFSC L B Δcka ⟨authH, some (l - 1), tStar⟩ j))
      L l (raw (2 + Δcka)) qep maxSkip tStar
      (raw (modeCfgEC OO ⟨true, some (l - 1), tStar⟩))
      (raw (⟨true, some (l - 1), tStar⟩ : Mode).policy) st q
  finish := rdsl [_, _] do
    sample (O := OO) (I := II) CKASamp.bit ()

local notation "redFSGen" =>
  redFSAuthDFShiftedPaperGenProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
    (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
    (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)

abbrev redFSAuthDFShiftedPaperProg (L B Δcka qep maxSkip j l tStar : ℕ) :
    CostedReduction OO II (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  redFSGen L B Δcka qep maxSkip j l tStar true

abbrev redFSAuthDFShiftedDir2PaperProg (L B qep maxSkip j l tStar : ℕ) :
    CostedReduction OO II (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (prngSMCodecDF KC Γ CCoins T I KR RSt K SS RS M E) .unit .unit .bool .bool :=
  redFSGen L B 0 qep maxSkip j l tStar false

theorem redFSAuthDFShiftedPaperProg_eval_clamp
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (L B B_q Δcka qep j l tStar : ℕ) (authH : Bool)
    (hInitA : ckaInitA = cka.initA) (hInitB : ckaInitB = cka.initB)
    (hSend : ckaSend = cka.send) (hRecv : ckaReceive = cka.receive)
    (hPrngInit : prngInit = prng.init) (hPrngUp : prngUp = prng.up)
    (hFsInitS : fsInitSender = fs.initSender) (hFsInitR : fsInitReceiver = fs.initReceiver)
    (hFsSend : fsSend = fs.send) (hFsRecv : fsReceive = fs.receive)
    (heqT : eqT = (· == ·)) (heqI : eqI = (· == ·))
    (heqM : eqM = (· == ·)) (heqE : eqE = (· == ·)) (hDefaultE : defaultE = default)
    (hSampKR : sampKR = ($ᵗ KR : ProbComp KR)) (hSampKC : sampKC = ($ᵗ KC : ProbComp KC))
    (hSampCCoins : sampCCoins = ($ᵗ CCoins : ProbComp CCoins))
    (hSampI : sampI = ($ᵗ I : ProbComp I)) (hSampK : sampK = ($ᵗ K : ProbComp K))
    (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    (redFSGen L B Δcka qep fs.maxSkip j l tStar authH).eval (fun _ => A) () =
      DeliverForge.redFSAuthDFShiftedPaperGen cka prng (fsClamp B fs) lam Δcka qep j l tStar
        authH A := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) qAdv := by
    refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]
  have hBit : ∀ {Γ'} (ρ' : Env Γ'),
      (@Comp.sample _ _ _ OO II _ CKASamp.bit .unit).eval ρ' =
        (sampleT Bool : TComp (FSAEAD.spec SS RS (Header T) M E) Bool) := fun ρ' => by
    simp only [Comp.eval, fsaeadHeaderAdIface, prngSamplers, ckaSamplers, sampleT]
    exact Engine.liftP_eq_liftM II (fun _ => rfl) ($ᵗ Bool)
  have hInit := initFSEStateC_eval (ckaSend := ckaSend) (ckaReceive := ckaReceive)
    (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqM := eqM) (eqE := eqE)
    (lam := lam) (defaultE := defaultE) (sampCCoins := sampCCoins)
    cka prng (fsClamp B fs) hInitA hInitB hPrngInit hPrngUp hFsInitS hFsInitR heqI
    hSampKR hSampKC hSampI hSampK L ⟨authH, some (l - 1), tStar⟩ j (.bool false)
    (Env.cons (t := (.unit : Ty S)) () .nil)
  unfold CostedReduction.eval redFSAuthDFShiftedPaperGenProg CostedReduction.impl
    DeliverForge.redFSAuthDFShiftedPaperGen
  dsimp only
  change _ = (runFSDFShiftedPaper (!authH) cka prng (fsClamp B fs) lam l Δcka qep tStar
    ⟨authH, some (l - 1), tStar⟩ ⟨true, some (l - 1), tStar⟩ j false A >>= fun _ => sampleT Bool)
  rw [runFSDFShiftedPaper_eq_bind_initFSRaw, eval_bind, hInit]
  simp only [bind_map_left, eval_ret, Expr.eval, Expr.v0, Env.get_cons_zero, bind_assoc, pure_bind]
  refine OracleComp.bind_congr_of_forall_mem_support
    (initFSRaw cka prng (fsClamp B fs) lam ⟨authH, some (l - 1), tStar⟩ j false) fun es₀ hes₀ => ?_
  have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (fsClamp B fs) lam ⟨authH, some (l - 1), tStar⟩ j
    false hqB hB1 hBB es₀ hes₀
  have ⟨hSim, _⟩ := simulateQ_implECDFShiftedPaper_fs_eq (ckaInitA := ckaInitA)
    (ckaInitB := ckaInitB) (prngInit := prngInit) (fsReceive := fsReceive) (lam := lam)
    (sampKR := sampKR) (sampKC := sampKC) (!authH) cka prng (fsClamp B fs) L B B_q l (2 + Δcka)
    Δcka qep tStar ⟨authH, some (l - 1), tStar⟩ ⟨true, some (l - 1), tStar⟩ j
    hSend hRecv hPrngUp hFsInitS hFsInitR hFsSend heqT heqI heqM heqE hDefaultE
    hSampCCoins hSampI hSampK (fun rs hdr e => by simp [fsClamp, hFsRecv]) hA' es₀ hInv₀
  have hms : (fsClamp B fs).maxSkip = fs.maxSkip := rfl
  dsimp only [Expr.v0] at hSim; rw [hms] at hSim; rw [hSim, bind_map_left]
  exact bind_congr fun ⟨_, _⟩ => hBit _

@[simp] theorem implECDFShiftedPaper_hooksFSC_queries (b1 : Bool)
    (L B l Δcka qep maxSkip tStar : ℕ) (mo mo' : Mode) (j : ℕ) {Γ'} (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L l (2 + Δcka) qep maxSkip tStar (modeCfgEC OO mo') mo'.policy es q).queries
      (fun _ => 1) (fun _ => 0) = 2 := by
  cases b1 <;> simp [implECDFShiftedPaperGen, implECShiftedPaperGen, transmitEC, challEC,
    deliverEC, injectECGen, injectEC, injectECB1, corrECShiftedPaper, deliverForgeECGen,
    deliverForgeEC, deliverForgeECB1, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
    hooksFSC, Comp.queries]

@[simp] theorem implECDFShiftedPaper_hooksFSC_decQueries (b1 : Bool)
    (L B l Δcka qep maxSkip tStar : ℕ) (mo mo' : Mode) (j : ℕ) {Γ'} (es : Expr OO Γ' esTyFS)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen b1 (hooksFSC (sampKR := sampKR) (sampKC := sampKC)
        (sampCCoins := sampCCoins) (sampI := sampI) (sampK := sampK) L B Δcka mo j)
      L l (2 + Δcka) qep maxSkip tStar (modeCfgEC OO mo') mo'.policy es q).queries
      fsHdrDecWt (fun _ => 0) = 1 := by
  cases b1 <;> simp [implECDFShiftedPaperGen, implECShiftedPaperGen, transmitEC, challEC,
    deliverEC, injectECGen, injectEC, injectECB1, corrECShiftedPaper, deliverForgeECGen,
    deliverForgeEC, deliverForgeECB1, vSendC, vSendStep1C, vRecvC, vRecvStep1C, commitEC,
    hooksFSC, Comp.queries]

theorem redFSAuthDFShiftedPaperProg_queries (L B Δcka qep maxSkip j l tStar : ℕ) (authH : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (q : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    FSAEAD.MakesAtMostQueries
      ((redFSGen L B Δcka qep maxSkip j l tStar authH).eval (fun _ => A) ()) (2 * q) := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q := by
    refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]
  have h := CostedReduction.queryBound_eval (redFSGen L B Δcka qep maxSkip j l tStar authH)
    (isGameQuery (G := FSAEAD.spec SS RS (Header T) M E))
    (fun _ => 1) (fun _ => 0) (fun _ _ _ => le_rfl)
    (fun n => by simp [isGameQuery, isQueryBoundP_query_iff]) (fun _ => A) q (fun _ => hA') ()
  have htot : (redFSGen L B Δcka qep maxSkip j l tStar authH).totalQueries
      (fun _ => 1) (fun _ => 0) q = q * 2 := by
    simp [CostedReduction.totalQueries, redFSAuthDFShiftedPaperGenProg, Comp.queries]
  rw [htot, Nat.mul_comm] at h
  refine h.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]

theorem redFSAuthDFShiftedPaperProg_decQueries (L B Δcka qep maxSkip j l tStar : ℕ) (authH : Bool)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt SS RS M CCoins E) (q : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A q) :
    FSAEAD.MakesAtMostDecQueries
      ((redFSGen L B Δcka qep maxSkip j l tStar authH).eval (fun _ => A) ()) q := by
  have hA' : A.IsQueryBoundP
      (isGameQuery (G := SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E))) q := by
    refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]
  have h := CostedReduction.queryBound_eval (redFSGen L B Δcka qep maxSkip j l tStar authH)
    (fun t => FSAEAD.isDecQuery (SS := SS) (RS := RS) (AD := Header T) (Msg := M) (C := E) t = true)
    fsHdrDecWt (fun _ => 0)
    (fun g x hg => by cases g <;> simp_all [FSAEAD.isDecQuery, fsHdrDecWt])
    (fun n => (isQueryBoundP_query_iff
      (spec := unifSpec + FSAEAD.spec SS RS (Header T) M E) _ (.inl n) 0).2 (fun h => by cases h))
    (fun _ => A) q (fun _ => hA') ()
  have htot : (redFSGen L B Δcka qep maxSkip j l tStar authH).totalQueries
      fsHdrDecWt (fun _ => 0) q = q := by
    simp [CostedReduction.totalQueries, redFSAuthDFShiftedPaperGenProg, Comp.queries]
  rwa [htot] at h

end HooksFSCDFShiftedPaper

section FromAEADPRGDFShiftedPaper

variable {MK C : Type}

theorem corrEShiftedPaper_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l B Δcka : ℕ) (mo : Mode) (j : ℕ) :
    DeliverForge.corrEShiftedPaper l (hooksFS cka prng (fsClamp B fs) Δcka mo j) =
      DeliverForge.corrEShiftedPaper l (hooksFS cka prng fs Δcka mo j) := by
  unfold DeliverForge.corrEShiftedPaper hooksFS fsClamp; rfl

theorem implEDFShiftedPaper_fsClamp_eq [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK))
    (l maxSkip B B_q q Δcka qep tStar : ℕ) (mo : Mode) (cfg : Config M) (π : Policy) (j : ℕ)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (t : (SM.specDF (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q (q + 1) es.g)
    (hExt : FSVROkStep maxSkip (B_q - (q + 1)) (es.h.ext.map Prod.snd)) :
    (DeliverForge.implEDFShiftedPaperGen b1 l
        (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
        (2 + Δcka) qep maxSkip tStar cfg π (.inr t)).run es =
      (DeliverForge.implEDFShiftedPaperGen b1 l
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
        (2 + Δcka) qep maxSkip tStar cfg π (.inr t)).run es := by
  have hkB : (B_q - (q + 1) + 1) * (maxSkip + 1) ≤ B :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.sub_le _ _) 1)).trans hB
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · change (transmitE _ _ _ _ (P, m, r)).run es = (transmitE _ _ _ _ (P, m, r)).run es
    unfold transmitE; rw [vSend_fsClamp_eq]
  · change (challE _ _ _ _ _ (P, m₀, m₁, r)).run es = (challE _ _ _ _ _ (P, m₀, m₁, r)).run es
    unfold challE; rw [vSend_fsClamp_eq]
  · change (deliverE _ maxSkip cfg (P, c)).run es = (deliverE _ maxSkip cfg (P, c)).run es
    unfold deliverE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs; · rfl
    rcases es.g.inTransit P.other c with _ | r; · rfl
    simp only [run_liftH_bind]
    rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j
      hkB es.g P (es.g.st P) c (some r) es.h (hVR P) hExt]; rfl
  · cases b1
    · change (injectE _ (2 + Δcka) qep cfg (P, c)).run es =
        (injectE _ (2 + Δcka) qep cfg (P, c)).run es
      unfold injectE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs; · rfl
      simp only [run_liftH_bind]
      rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j
        hkB es.g P (es.g.st P) c none es.h (hVR P) hExt]; rfl
    · exact injectEB1_fsClamp_eq cka prng ae G maxSkip B B_q q Δcka qep tStar cfg mo j hB es
        (P, c) hVR hExt
  · change (DeliverForge.corrEShiftedPaper l _ π P).run es =
      (DeliverForge.corrEShiftedPaper l _ π P).run es
    rw [corrEShiftedPaper_fsClamp_eq]
  · cases b1
    · change (DeliverForge.deliverForgeE _ (2 + Δcka) qep cfg (P, c, c')).run es =
        (DeliverForge.deliverForgeE _ (2 + Δcka) qep cfg (P, c, c')).run es
      unfold DeliverForge.deliverForgeE; simp only [StateT.run_bind, StateT.run_get, pure_bind]
      split_ifs; · rfl
      rcases es.g.inTransit P.other c with _ | r; · rfl
      dsimp only; split_ifs; · rfl
      simp only [run_liftH_bind]
      rw [vRecv_fsClamp_eq cka prng ae G maxSkip B (B_q - (q + 1)) Δcka mo j
        hkB es.g P (es.g.st P) c' none es.h (hVR P) hExt]; rfl
    · exact deliverForgeEB1_fsClamp_eq cka prng ae G maxSkip B B_q q Δcka qep tStar cfg mo j hB es
        (P, c, c') hVR hExt

theorem corrEShiftedPaper_ext_snd_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK))
    (l maxSkip k Δcka : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C))) (P : Party)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        ((DeliverForge.corrEShiftedPaper l
          (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          π P).run es)).run st),
      FSVROkStep maxSkip k (z.1.2.h.ext.map Prod.snd) := by
  intro z hz
  unfold DeliverForge.corrEShiftedPaper abortE at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz
  by_cases href : (es.abort || es.g.win || !(es.g.corrAllowedPaper P))
  · simp only [href, ↓reduceIte, StateT.run_pure, simulateQ_pure, support_pure,
      Set.mem_singleton_iff] at hz; subst hz; exact hExt
  · simp only [href, Bool.false_eq_true, ↓reduceIte] at hz
    by_cases hdoom : (π.leakDoom es.g (DeliverForge.afterCorrShifted l es.g P) || π.corrDoom es.g P)
    · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
        pure_bind, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hExt
    · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind] at hz
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
      obtain ⟨⟨⟨revRes, h'⟩, st'⟩, hrev, hz⟩ := hz
      have hExt' := fsReveal_ext_snd_fromAEADPRG cka prng ae G maxSkip k Δcka mo j
        es.g P (es.g.st P) es.h st hExt hSt ((revRes, h'), st') hrev
      rcases revRes with _ | stP <;>
        (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
           simulateQ_pure, support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hExt')

theorem implEDFShiftedPaper_ext_snd_fromAEADPRG [DecidableEq T] [DecidableEq I] [DecidableEq M]
    [DecidableEq C] [Inhabited C] [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK))
    (l maxSkip k Δcka qep tStar : ℕ) (mo : Mode) (cfg : Config M) (π : Policy) (j : ℕ)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (q : (SM.specDF (PartyState Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK)) M CCoins (Header T × (ℕ × C))).Domain)
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hVR : ∀ P t₀ v, (es.g.st P).vR t₀ = some v → FSVROkStep maxSkip k v)
    (hExt : FSVROkStep maxSkip k (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip k st.receiverState) :
    ∀ z ∈ support ((simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        ((DeliverForge.implEDFShiftedPaperGen b1 l
          (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
           (2 + Δcka) qep maxSkip tStar cfg π (.inr q)).run es)).run st),
      FSVROkStep maxSkip (k + 1) (z.1.2.h.ext.map Prod.snd) := by
  intro ⟨⟨out, es'⟩, st'⟩ hz
  have hExt1 : FSVROkStep maxSkip (k + 1) (es.h.ext.map Prod.snd) := hExt.mono (Nat.le_succ k)
  rcases q with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    change (out, es') ∈ support ((transmitE _ _ _ _ (P, m, r)).run es) at hmem
    unfold transmitE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hep] at hmem; split_ifs at hmem
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt1
        · simp only [run_liftH_bind, mem_support_bind_iff] at hmem
          obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
          have hext' := vSend_ext_snd cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
            Δcka mo j s₁ P (s₁.st P) m none r es.h (vsRes, h') hvs
          rcases vsRes with _ | ⟨st₁, ct⟩ <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt1)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    change (out, es') ∈ support ((challE _ _ _ _ _ (P, m₀, m₁, r)).run es) at hmem
    unfold challE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    by_cases hab : (es.abort || es.g.win) = true
    · simp only [hab, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
        Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hmem
      rcases hep : es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
      · simp only [hep, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [hep] at hmem
        by_cases hch : (!(s₁.safeCh (2 + Δcka) P) || !(cfg.challAllowedIn (s₁.epoch P)))
        · simp only [hch, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt1
        · simp only [hch, Bool.false_eq_true, ↓reduceIte] at hmem
          by_cases hdoom : π.leakDoom es.g s₁
          · simp only [hdoom, ↓reduceIte, StateT.run_bind, StateT.run_modify, StateT.run_pure,
              pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt1
          · simp only [hdoom, Bool.false_eq_true, ↓reduceIte, run_liftH_bind,
              mem_support_bind_iff] at hmem
            obtain ⟨⟨vsRes, h'⟩, hvs, hmem⟩ := hmem
            have hext' := vSend_ext_snd cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
              Δcka mo j s₁ P (s₁.st P) _ (some (m₀, m₁)) r es.h (vsRes, h') hvs
            rcases vsRes with _ | ⟨st₁, ct⟩ <;>
              (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                 support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
               rcases hmem with ⟨_, rfl⟩; dsimp only at hext' ⊢; rw [hext']; exact hExt1)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    change (out, es') ∈ support ((deliverE _ maxSkip _ (P, c)).run es) at hmem
    unfold deliverE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩; exact hExt1
    · rcases htr : es.g.inTransit P.other c with _ | r
      · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [htr, run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) c (some r) es.h (hVR P) hExt (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st₁, t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · split_ifs at hmem <;>
            (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
               support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
             rcases hmem with ⟨_, rfl⟩; exact hExt')
        · simp only [StateT.run_bind, commitE_fs_eq, pure_bind, StateT.run_modify,
            StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    cases b1
    · change (out, es') ∈ support ((injectE _ (2 + Δcka) qep _ (P, c)).run es) at hmem
      unfold injectE abortE at hmem; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      split_ifs at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · simp only [run_liftH_bind, mem_support_bind_iff] at hmem
        obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
        have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
          es.g P (es.g.st P) c none es.h (hVR P) hExt (vrRes, h') hvr
        rcases vrRes with _ | _ | ⟨st₁, t', i', m'⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
          rcases hmem with ⟨_, rfl⟩; exact hExt'
        · by_cases hqep : qep + 1 < t'
          · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
              Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
          · simp only [hqep, ↓reduceIte] at hmem
            by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
            · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
                StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
            · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
              split_ifs at hmem <;>
                (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                   support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
                 rcases hmem with ⟨_, rfl⟩; exact hExt')
    · exact injectEB1_ext_snd cka prng ae G maxSkip k Δcka qep tStar cfg mo j es (P, c)
        hVR hExt (out, es') hmem
  · exact (corrEShiftedPaper_ext_snd_fromAEADPRG cka prng ae G l maxSkip k Δcka mo π j es P st hExt
      hSt ((out, es'), st') hz).mono (Nat.le_succ k)
  · have hmem := fst_mem_support_of_mem_support_simulateQ_run _ _ st hz
    cases b1
    · change (out, es') ∈
        support ((DeliverForge.deliverForgeE _ (2 + Δcka) qep _ (P, c, c')).run es) at hmem
      unfold DeliverForge.deliverForgeE abortE at hmem
      simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
      split_ifs at hmem
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
        rcases hmem with ⟨_, rfl⟩; exact hExt1
      · rcases htr : es.g.inTransit P.other c with _ | r
        · simp only [htr, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt1
        · simp only [htr] at hmem; split_ifs at hmem
          · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
            rcases hmem with ⟨_, rfl⟩; exact hExt1
          · simp only [run_liftH_bind, mem_support_bind_iff] at hmem
            obtain ⟨⟨vrRes, h'⟩, hvr, hmem⟩ := hmem
            have hExt' := vRecv_ext_snd cka prng ae G maxSkip k Δcka mo j
              es.g P (es.g.st P) c' none es.h (hVR P) hExt (vrRes, h') hvr
            rcases vrRes with _ | _ | ⟨st₁, t', i', m'⟩
            · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
              rcases hmem with ⟨_, rfl⟩; exact hExt'
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
                Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
            · by_cases hqep : (decide (qep + 1 < t') || (t' != r.pos.epoch))
              · simp only [hqep, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                  Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
              · simp only [hqep, Bool.false_eq_true, ↓reduceIte] at hmem
                by_cases htriv : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩
                · simp only [htriv, ↓reduceIte, StateT.run_bind, commitE_fs_eq, pure_bind,
                    StateT.run_modify, StateT.run_pure, support_pure, Set.mem_singleton_iff,
                    Prod.mk.injEq] at hmem; rcases hmem with ⟨_, rfl⟩; exact hExt'
                · simp only [htriv, Bool.false_eq_true, ↓reduceIte] at hmem
                  split_ifs at hmem <;>
                    (simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
                       support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem;
                     rcases hmem with ⟨_, rfl⟩; exact hExt')
    · exact deliverForgeEB1_ext_snd cka prng ae G maxSkip k Δcka qep tStar cfg mo j es (P, c, c')
        hVR hExt (out, es') hmem

theorem qb_corrEShiftedPaper_zero {Q : (ReductionsQueries.RSpec SS RS T M E).Domain → Prop}
    [DecidablePred Q] (hQcs : ¬ Q (.inr (.inl (.inl (.inl (.inr ()))))))
    (hQcr : ¬ Q (.inr (.inl (.inl (.inr ())))))
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l Δcka : ℕ) (mo : Mode) (π : Policy) (j : ℕ)
    (P : Party) : ReductionsQueries.QB Q
      (DeliverForge.corrEShiftedPaper l (hooksFS cka prng fs Δcka mo j) π P) 0 := by
  unfold DeliverForge.corrEShiftedPaper
  refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
  dsimp only; split_ifs
  · exact ReductionsQueries.qb_pure none 0
  · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
      ReductionsQueries.qb_pure none 0
  · refine ReductionsQueries.qb_bind0 (ReductionsQueries.qb_liftH
      (ReductionsQueries.qb_reveal_zero hQcs hQcr cka prng fs Δcka mo j es.g P (es.g.st P)))
      fun res => ?_
    rcases res with _ | st
    · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
        ReductionsQueries.qb_pure none 0
    · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
        ReductionsQueries.qb_pure (some st) 0

theorem qb_implEDFShiftedPaper_inr_one {Q : (ReductionsQueries.RSpec SS RS T M E).Domain → Prop}
    [DecidablePred Q] (hQu : ∀ u, ¬ Q (.inl u))
    (hQt : ∀ a m, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inl (a, m))))))))
    (hQch : ∀ a m₀ m₁, ¬ Q (.inr (.inl (.inl (.inl (.inl (.inr (a, m₀, m₁))))))))
    (hQcs : ¬ Q (.inr (.inl (.inl (.inl (.inr ())))))) (hQcr : ¬ Q (.inr (.inl (.inl (.inr ())))))
    [DecidableEq M] [DecidableEq T] [DecidableEq E] [DecidableEq I] [Inhabited E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (l Δcka qep tStar : ℕ) (mo : Mode)
    (cfg : Config M) (π : Policy) (j : ℕ)
    (t : (SM.specDF (PartyState Γ T RSt SS RS) M CCoins (Header T × E)).Domain) :
    ReductionsQueries.QB Q
      (DeliverForge.implEDFShiftedPaperGen b1 l (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep
        fs.maxSkip tStar cfg π (.inr t)) 1 := by
  rcases t with ((((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P) | ⟨P, c, c'⟩
  · refine ReductionsQueries.qb_mono (by
      change ReductionsQueries.QB Q
        (transmitE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep π (P, m, r)) 0
      unfold transmitE; refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
      by_cases h1 : (es.abort || es.g.win) = true
      · simp only [h1, ↓reduceIte]; exact ReductionsQueries.qb_pure none 0
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · exact ReductionsQueries.qb_pure none 0
        · dsimp only; split_ifs
          · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
              ReductionsQueries.qb_pure none 0
          · refine ReductionsQueries.qb_bind0 (ReductionsQueries.qb_liftH
              (ReductionsQueries.qb_vSend_zero hQu hQt hQch hQcs cka prng fs Δcka mo j s₁ P
                (s₁.st P) m none r)) fun res => ?_
            rcases res with _ | sc
            · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
                ReductionsQueries.qb_pure none 0
            · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                ReductionsQueries.qb_pure (some sc.2) 0) (by omega)
  · refine ReductionsQueries.qb_mono (by
      change ReductionsQueries.QB Q
        (challE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep cfg π (P, m₀, m₁, r)) 0
      unfold challE; refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
      by_cases h1 : (es.abort || es.g.win) = true
      · simp only [h1, ↓reduceIte]; exact ReductionsQueries.qb_pure none 0
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        rcases es.g.epMgmt (2 + Δcka) qep P r.isSome with _ | s₁
        · exact ReductionsQueries.qb_pure none 0
        · dsimp only; by_cases h2 : (!s₁.safeCh (2 + Δcka) P || !cfg.challAllowedIn (s₁.epoch P)) = true
          · simp only [h2, ↓reduceIte]; exact ReductionsQueries.qb_pure none 0
          · simp only [h2, Bool.false_eq_true, ↓reduceIte]
            by_cases h3 : π.leakDoom es.g s₁ = true
            · simp only [h3, ↓reduceIte]
              exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
                ReductionsQueries.qb_pure none 0
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              refine ReductionsQueries.qb_bind0 (ReductionsQueries.qb_liftH
                (ReductionsQueries.qb_vSend_zero hQu hQt hQch hQcs cka prng fs Δcka mo j s₁ P
                  (s₁.st P) _ (some (m₀, m₁)) r)) fun res => ?_
              rcases res with _ | sc
              · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
                  ReductionsQueries.qb_pure none 0
              · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                  ReductionsQueries.qb_pure (some sc.2) 0) (by omega)
  · change ReductionsQueries.QB Q (deliverE (hooksFS cka prng fs Δcka mo j) fs.maxSkip cfg (P, c)) 1
    unfold deliverE; refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
    by_cases h1 : (es.abort || es.g.win) = true
    · simp only [h1, ↓reduceIte]; exact ReductionsQueries.qb_pure none 1
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      rcases es.g.inTransit P.other c with _ | r
      · exact ReductionsQueries.qb_pure none 1
      · dsimp only; refine ReductionsQueries.qb_bind_r (ReductionsQueries.qb_liftH
          (ReductionsQueries.qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c (some r)))
          fun res => ?_
        rcases res with _ | _ | ⟨st', t', i', m'⟩
        · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
            ReductionsQueries.qb_pure none 0
        · dsimp only; split_ifs
          · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
              ReductionsQueries.qb_pure (some RecvResult.rejected) 0
          · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
        · dsimp only; refine ReductionsQueries.qb_bind0
            (ReductionsQueries.qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st' r.pos)
            fun s₁? => ?_
          rcases s₁? with _ | s₁
          · exact ReductionsQueries.qb_pure none 0
          · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
              ReductionsQueries.qb_pure _ 0
  · cases b1
    · change ReductionsQueries.QB Q
        (injectE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep cfg (P, c)) 1
      unfold injectE; refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
      dsimp only
      by_cases h1 : (es.abort || es.g.win || (es.g.inTransit P.other c).isSome ||
          !es.g.safeInj (2 + Δcka)) = true
      · simp only [h1, ↓reduceIte]; exact ReductionsQueries.qb_pure none 1
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]
        refine ReductionsQueries.qb_bind_r (ReductionsQueries.qb_liftH
          (ReductionsQueries.qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c none))
          fun res => ?_
        rcases res with _ | _ | ⟨st', t', i', m'⟩
        · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
            ReductionsQueries.qb_pure none 0
        · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
        · dsimp only; by_cases h2 : qep + 1 < t'
          · simp only [h2, ↓reduceIte]; exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
          · simp only [h2, ↓reduceIte]
            by_cases h3 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
            · simp only [h3, ↓reduceIte]
              refine ReductionsQueries.qb_bind0
                (ReductionsQueries.qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st'
                  ⟨P.other, t', i'⟩) fun s₁? => ?_
              rcases s₁? with _ | s₁
              · exact ReductionsQueries.qb_pure none 0
              · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                  ReductionsQueries.qb_pure _ 0
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]; split_ifs
              · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                  ReductionsQueries.qb_pure (some RecvResult.rejected) 0
              · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
    · exact qb_injectEB1_one hQu cka prng fs Δcka qep tStar cfg mo j (P, c)
  · exact ReductionsQueries.qb_mono
      (qb_corrEShiftedPaper_zero hQcs hQcr cka prng fs l Δcka mo π j P) (by omega)
  · cases b1
    · change ReductionsQueries.QB Q
        (DeliverForge.deliverForgeE (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep cfg (P, c, c')) 1
      unfold DeliverForge.deliverForgeE
      refine ReductionsQueries.qb_bind0 ReductionsQueries.qb_get fun es => ?_
      dsimp only; by_cases hab : (es.abort || es.g.win) = true
      · simp only [hab, ↓reduceIte]; exact ReductionsQueries.qb_pure none 1
      · simp only [hab, Bool.false_eq_true, ↓reduceIte]
        rcases htr : es.g.inTransit P.other c with _ | r
        · exact ReductionsQueries.qb_pure none 1
        · dsimp only
          by_cases hbad :
              ((es.g.inTransit P.other c').isSome || es.g.comp.contains r.pos || c.1 != c'.1) = true
          · simp only [hbad, ↓reduceIte]; exact ReductionsQueries.qb_pure none 1
          · simp only [hbad, Bool.false_eq_true, ↓reduceIte]
            refine ReductionsQueries.qb_bind_r (ReductionsQueries.qb_liftH
              (ReductionsQueries.qb_vRecv_one hQu cka prng fs Δcka mo j es.g P (es.g.st P) c' none))
              fun res => ?_
            rcases res with _ | _ | ⟨st', t', i', m'⟩
            · exact ReductionsQueries.qb_bind0 ReductionsQueries.qb_abortE fun _ =>
                ReductionsQueries.qb_pure none 0
            · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
            · dsimp only; by_cases h2 : (decide (qep + 1 < t') || (t' != r.pos.epoch)) = true
              · simp only [h2, ↓reduceIte]
                exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
              · simp only [h2, Bool.false_eq_true, ↓reduceIte]
                by_cases h3 : es.g.trivial (2 + Δcka) ⟨P.other, t', i'⟩ = true
                · simp only [h3, ↓reduceIte]
                  refine ReductionsQueries.qb_bind0
                    (ReductionsQueries.qb_commitE cka prng fs Δcka mo j es.g P (es.g.st P) st'
                      ⟨P.other, t', i'⟩) fun s₁? => ?_
                  rcases s₁? with _ | s₁
                  · exact ReductionsQueries.qb_pure none 0
                  · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                      ReductionsQueries.qb_pure _ 0
                · simp only [h3, Bool.false_eq_true, ↓reduceIte]; split_ifs
                  · exact ReductionsQueries.qb_bind0 (ReductionsQueries.qb_modify _) fun _ =>
                      ReductionsQueries.qb_pure (some RecvResult.rejected) 0
                  · exact ReductionsQueries.qb_pure (some RecvResult.rejected) 0
    · exact qb_deliverForgeEB1_one hQu cka prng fs Δcka qep tStar cfg mo j (P, c, c')

theorem simulateQ_implEDFShiftedPaper_fsClamp_fromAEADPRG_eq [DecidableEq T] [DecidableEq I]
    [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (b1 : Bool) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK))
    (fs₀ : FSAEADScheme K (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (L l B B_q Δcka qep maxSkip tStar : ℕ) (mo : Mode) (cfg : Config M) (π : Policy) (j : ℕ)
    (hfs₀ : fs₀ = FSAEAD.fromAEADPRG ae G maxSkip)
    (hB : (B_q + 1) * (maxSkip + 1) ≤ B)
    {α : Type} {oa : OracleComp (unifSpec + SM.specDF
      (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
      M CCoins (Header T × (ℕ × C))) α}
    {q : ℕ}
    (hoa : oa.IsQueryBoundP
      (isGameQuery (G := SM.specDF
        (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
        M CCoins (Header T × (ℕ × C)))) q)
    (es : EState (VP Γ T RSt (Option (FSAEAD.RatchetSenderState K))
      (Option (FSAEAD.RatchetReceiverState K MK))) M (Header T × (ℕ × C))
      (FSState T RSt K I (FSAEAD.RatchetSenderState K)
        (FSAEAD.RatchetReceiverState K MK) (ℕ × C)))
    (st : FSAEAD.State (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK)
      (Header T) M (ℕ × C))
    (hInv : SMEngineInv L B_q q es.g)
    (hVR : SMVRInv (FSVROkStep maxSkip) B_q q es.g)
    (hExt : FSVROkStep maxSkip (B_q - q) (es.h.ext.map Prod.snd))
    (hSt : RSReach maxSkip (B_q - q) st.receiverState) :
    (simulateQ (fsFullImpl fs₀)
      ((simulateQ (DeliverForge.implEDFShiftedPaperGen b1 l
        (hooksFS cka prng (fsClamp B fs₀) Δcka mo j)
        (2 + Δcka) qep maxSkip tStar cfg π) oa).run es)).run st =
    (simulateQ (fsFullImpl fs₀)
      ((simulateQ (DeliverForge.implEDFShiftedPaperGen b1 l
        (hooksFS cka prng fs₀ Δcka mo j)
        (2 + Δcka) qep maxSkip tStar cfg π) oa).run es)).run st := by
  subst hfs₀
  induction oa using OracleComp.inductionOn generalizing q es st with
  | pure x => simp only [simulateQ_pure, StateT.run_pure]
  | query_bind qy mx ih =>
    rw [isQueryBoundP_query_bind_iff] at hoa; rcases hoa with ⟨hq0, hmx⟩
    rw [simulateQ_query_bind, simulateQ_query_bind, StateT.run_bind, StateT.run_bind,
      simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
    have hLift : ∀ {M' : Type → Type} [Monad M'] {σ' α' : Type} (m : StateT σ' M' α') (s : σ'),
        (liftM m : StateT σ' M' α').run s = m.run s := fun _ _ => rfl
    rw [hLift, hLift]; simp only [OracleQuery.input_query, OracleQuery.cont_query]
    rcases qy with n | t_sm
    · simp only [isGameQuery, ↓reduceIte] at hmx
      have hInl1 : (DeliverForge.implEDFShiftedPaperGen b1 l
          (hooksFS cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) Δcka mo j)
          (2 + Δcka) qep maxSkip tStar cfg π (.inl n)).run es = (coinsE n).run es := rfl
      have hInl2 : (DeliverForge.implEDFShiftedPaperGen b1 l
          (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (2 + Δcka) qep maxSkip tStar cfg π (.inl n)).run es = (coinsE n).run es := rfl
      rw [hInl1, hInl2]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      simp only [coinsE, StateT.run_lift, mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem1
      obtain ⟨_, _, _, rfl⟩ := hmem1
      have hQbCoins : ((coinsE n).run es').IsQueryBoundP
          (ReductionsQueries.QFSDec (FSAEAD.RatchetSenderState K)
            (FSAEAD.RatchetReceiverState K MK) T M (ℕ × C)) 0 :=
        ReductionsQueries.qb_coinsE (ReductionsQueries.hQu_QFSDec _ _ T M (ℕ × C)) n es'
      have hSt' : RSReach maxSkip (B_q - q) st'.receiverState := by
        simpa using receiverState_reach_of_isDecQuery_bound ae G maxSkip hQbCoins st hSt
          ((u, es'), st') hmem
      exact ih u (hmx u) es' st' hInv hVR hExt hSt'
    · simp only [isGameQuery, ↓reduceIte] at hq0 hmx
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq0.resolve_left (by decide); omega⟩
      rw [implEDFShiftedPaper_fsClamp_eq b1 cka prng ae G l maxSkip B B_q q' Δcka qep tStar mo
        cfg π j hB es t_sm hVR hExt]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨⟨u, es'⟩, st'⟩ hmem => ?_
      have hmem1 := fst_mem_support_of_mem_support_simulateQ_run _ _ st hmem
      have hInv' := implEDFShiftedPaper_inv b1
        (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j) l cfg π es t_sm hInv
        (u, es') hmem1
      have hVR' : SMVRInv (FSVROkStep maxSkip) B_q q' es'.g :=
        implEDFShiftedPaper_vrInv b1 (hooksFS cka prng (FSAEAD.fromAEADPRG ae G maxSkip) Δcka mo j)
          (hooksFS_vrInv_fromAEADPRG cka prng ae G maxSkip Δcka mo j)
          l cfg π es t_sm hInv hVR (u, es') hmem1
      have hBq : B_q - (q' + 1) + 1 ≤ B_q - q' := by have := hInv.1; omega
      have hExt' : FSVROkStep maxSkip (B_q - q') (es'.h.ext.map Prod.snd) :=
        (implEDFShiftedPaper_ext_snd_fromAEADPRG b1 cka prng ae G l maxSkip (B_q - (q' + 1))
          Δcka qep tStar mo cfg π j es t_sm st (fun P _ _ hv => hVR P _ _ hv) hExt hSt
          ((u, es'), st') hmem).mono hBq
      have hSt' : RSReach maxSkip (B_q - q') st'.receiverState := by
        have hQbStep := qb_implEDFShiftedPaper_inr_one
          (ReductionsQueries.hQu_QFSDec _ _ T M (ℕ × C))
          (ReductionsQueries.hQt_QFSDec _ _ T M (ℕ × C))
          (ReductionsQueries.hQch_QFSDec _ _ T M (ℕ × C))
          (ReductionsQueries.hQcs_QFSDec _ _ T M (ℕ × C))
          (ReductionsQueries.hQcr_QFSDec _ _ T M (ℕ × C))
          b1 cka prng (FSAEAD.fromAEADPRG ae G maxSkip) l Δcka qep tStar mo cfg π j t_sm es
        exact (receiverState_reach_of_isDecQuery_bound ae G maxSkip hQbStep st hSt
          ((u, es'), st') hmem).mono hBq
      exact ih u (by simpa using hmx u) es' st' hInv' hVR' hExt' hSt'

theorem redFSAuthDFShiftedPaperGen_fsClamp_advantage_fromAEADPRG
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq C] [Inhabited C]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (ae : AEADScheme MK (ℕ × Header T) M C) (G : ℕ → PRGScheme K (K × MK)) (maxSkip : ℕ)
    (L B B_q Δcka qep j l tStar : ℕ) (authH : Bool) (lam : I)
    (hFsB : (B_q + 1) * (maxSkip + 1) ≤ B) (hB1 : B_q + 1 ≤ L) (hBB : B_q * B_q ≤ L * L)
    (A : DeliverForge.SchemeAdversaryDF Γ T RSt (FSAEAD.RatchetSenderState K)
      (FSAEAD.RatchetReceiverState K MK) M CCoins (ℕ × C)) (qAdv : ℕ)
    (hA : DeliverForge.MakesAtMostQueriesDF A qAdv) (hqB : qAdv ≤ B_q) :
    FSAEAD.advantage (FSAEAD.fromAEADPRG ae G maxSkip)
      (DeliverForge.redFSAuthDFShiftedPaperGen cka prng
        (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) lam Δcka qep j l tStar authH A) =
    FSAEAD.advantage (FSAEAD.fromAEADPRG ae G maxSkip)
      (DeliverForge.redFSAuthDFShiftedPaperGen cka prng
        (FSAEAD.fromAEADPRG ae G maxSkip) lam Δcka qep j l tStar authH A) := by
  have hGame :
      FSAEAD.game (FSAEAD.fromAEADPRG ae G maxSkip)
        (DeliverForge.redFSAuthDFShiftedPaperGen cka prng
          (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) lam Δcka qep j l tStar authH A) =
      FSAEAD.game (FSAEAD.fromAEADPRG ae G maxSkip)
        (DeliverForge.redFSAuthDFShiftedPaperGen cka prng
          (FSAEAD.fromAEADPRG ae G maxSkip) lam Δcka qep j l tStar authH A) := by
    unfold FSAEAD.game DeliverForge.redFSAuthDFShiftedPaperGen
    refine bind_congr fun b => bind_congr fun k => ?_
    dsimp only
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind, bind_assoc, bind_assoc]
    let mo : Mode := ⟨authH, some (l - 1), tStar⟩
    let mo' : Mode := ⟨true, some (l - 1), tStar⟩
    let st₀ := FSAEAD.initState (FSAEAD.fromAEADPRG ae G maxSkip) k b
    have hRun : (simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        (runFSDFShiftedPaper (!authH) cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip))
           lam l Δcka qep tStar mo mo' j false A)).run st₀ =
      (simulateQ (fsFullImpl (FSAEAD.fromAEADPRG ae G maxSkip))
        (runFSDFShiftedPaper (!authH) cka prng (FSAEAD.fromAEADPRG ae G maxSkip)
          lam l Δcka qep tStar mo mo' j false A)).run st₀ := by
      have hA' : A.IsQueryBoundP
          (isGameQuery (G := SM.specDF
            (PartyState Γ T RSt (FSAEAD.RatchetSenderState K) (FSAEAD.RatchetReceiverState K MK))
            M CCoins (Header T × (ℕ × C)))) qAdv := by
        refine hA.of_imp (fun x hx => ?_); rcases x with _ | _ <;> simp_all [isGameQuery]
      rw [runFSDFShiftedPaper_eq_bind_initFSRaw, runFSDFShiftedPaper_eq_bind_initFSRaw]
      have hInitEq :
          initFSRaw cka prng (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)) lam mo j false =
            initFSRaw cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j false := rfl
      rw [hInitEq, simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
      refine OracleComp.bind_congr_of_forall_mem_support _ fun ⟨es₀, st₁⟩ hmem₀ => ?_
      have hes₀ := fst_mem_support_of_mem_support_simulateQ_run _ _ st₀ hmem₀
      have ⟨hInv₀, _⟩ := initFSRaw_inv cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j false
        hqB hB1 hBB es₀ hes₀
      have ⟨hVR₀, hext₀⟩ := initFSRaw_vrInv_fromAEADPRG cka prng ae G maxSkip lam mo j false
        B_q qAdv es₀ hes₀
      have hExt₀ : FSVROkStep maxSkip (B_q - qAdv) (es₀.h.ext.map Prod.snd) := by
        simp [hext₀, FSVROkStep]
      have hSt₁ : RSReach maxSkip (B_q - qAdv) st₁.receiverState :=
        (receiverState_reach_of_isDecQuery_bound ae G maxSkip
          (isQueryBoundP_initFSRaw_dec cka prng (FSAEAD.fromAEADPRG ae G maxSkip) lam mo j false)
          st₀ (RSReach.init ae G maxSkip k) (es₀, st₁) hmem₀).mono (Nat.zero_le _)
      rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, StateT.run_bind]
      have hSim := simulateQ_implEDFShiftedPaper_fsClamp_fromAEADPRG_eq (!authH) cka prng ae G
        (FSAEAD.fromAEADPRG ae G maxSkip) L l B B_q Δcka qep maxSkip tStar
        mo mo'.cfg mo'.policy j rfl hFsB hA' es₀ st₁ hInv₀.sm hVR₀ hExt₀ hSt₁
      have hms1 : (fsClamp B (FSAEAD.fromAEADPRG ae G maxSkip)).maxSkip = maxSkip := rfl
      have hms2 : (FSAEAD.fromAEADPRG ae G maxSkip).maxSkip = maxSkip := rfl
      rw [hms1, hms2, hSim]
    simp only [fsFullImpl, runFSDFShiftedPaper, mo, mo', st₀, Mode.cfg, Mode.policy,
      ↓reduceIte] at hRun
    rw [hRun]
  unfold FSAEAD.advantage; rw [hGame]

end FromAEADPRGDFShiftedPaper

end CryptoGames.SM.Construction
namespace CryptoGames.SM.Engine

open ReductionDsl OracleSpec OracleComp Construction CKA PRFPRNG

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "psTy" => ckaPsTy KC Γ CCoins T I KR RSt K SS RS M E

section PaperCostDominance

variable {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E}

local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE

theorem cCorrAllowedPaperE_cost_le {O' : Ops S} {vpT : Ty S} {Γ'} (L : ℕ)
    (s : Expr O' Γ' (cGsTy vpT)) (p : Expr O' Γ' .bool) :
    (cCorrAllowedPaperE L s p).cost ≤ (cCorrAllowedE L s p).cost := by
  unfold cCorrAllowedPaperE cCorrAllowedE; dsimp only [Expr.cost]; omega

theorem corrECPaper_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L : ℕ) (π : Policy) {Γ'}
    (es : Expr OO Γ' (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO Γ' .bool) :
    (corrECPaper hk L π es p).cost ≤ (corrEC hk L π es p).cost := by
  let vpT := @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  unfold corrECPaper corrEC
  have h := cCorrAllowedPaperE_cost_le (O' := OO) (vpT := vpT)
    (Γ' := .prod (esTy vpT hsT) .bool :: Γ') L (esG (.fst .v0)) (.snd .v0)
  dsimp only [Comp.cost, Expr.cost, orE]; omega

theorem implECDFPaper_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L Δ qep maxSkip : ℕ) (cfg : ConfigEC OO) (π : Policy)
    {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFPaper hk L Δ qep maxSkip cfg π es q).cost ≤
      (implECDF hk L Δ qep maxSkip cfg π es q).cost := by
  let esT := esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT
  let smQ := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smQDF := ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  unfold implECDFPaper implECDF implECPaper implEC
  have h := corrECPaper_cost_le hk L π
    (Γ' := .bool :: .prod esT smQ :: smQ :: .prod esT smQDF :: Γ') (.fst .v1) .v0
  dsimp only [Comp.cost, Expr.cost]; omega

theorem corrECShiftedPaper_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L l : ℕ) (π : Policy) {Γ'}
    (es : Expr OO Γ' (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (p : Expr OO Γ' .bool) :
    (corrECShiftedPaper hk L l π es p).cost ≤ (corrECShifted hk L l π es p).cost := by
  let vpT := @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  unfold corrECShiftedPaper corrECShifted
  have h := cCorrAllowedPaperE_cost_le (O' := OO) (vpT := vpT)
    (Γ' := .prod (esTy vpT hsT) .bool :: Γ') L (esG (.fst .v0)) (.snd .v0)
  dsimp only [Comp.cost, Expr.cost, orE]; omega

theorem implECDFShiftedPaper_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L l Δ qep maxSkip tStar : ℕ) (cfg : ConfigEC OO)
    (π : Policy) {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen false hk L l Δ qep maxSkip tStar cfg π es q).cost ≤
      (implECDFShifted hk L l Δ qep maxSkip cfg π es q).cost := by
  let esT := esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT
  let smQ := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smQDF := ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 := .prod esT smQDF :: Γ'
  let Γ1 := .prod esT smQ :: smQ :: Γ0
  let smQ1 := match smQ with | .sum a _ => a | t => t
  have hij : (injectECGen false hk L Δ qep tStar cfg
      (Γ' := .prod .bool (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E) :: smQ1 :: Γ1)
      (.fst .v2) .v0).cost = (injectEC hk L Δ qep cfg (.fst .v2) .v0).cost := rfl
  have hdf : (deliverForgeECGen false hk L Δ qep tStar cfg
      (Γ' := .prod .bool (.prod (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :: Γ0) (.fst .v1) .v0).cost =
      (deliverForgeEC hk L Δ qep cfg (.fst .v1) .v0).cost := rfl
  have h := corrECShiftedPaper_cost_le hk L l π (Γ' := .bool :: Γ1) (.fst .v1) .v0
  unfold implECDFShiftedPaperGen implECDFShifted implECShiftedPaperGen implECShifted
  dsimp only [Comp.cost, Expr.cost]; omega

private theorem add_eq_both {a1 a2 b1 b2 : ℕ} (ha : a1 = a2) (hb : b1 = b2) :
    a1 + b1 + 1 = a2 + b2 + 1 := by omega
private theorem max_eq_right {a1 a2 b c1 c2 : ℕ} (ha : a1 = a2) (hc : c1 = c2) :
    a1 + max b c1 + 1 = a2 + max b c2 + 1 := by omega
private theorem cEpMgmtE_cost_2_eq_3 {O' : Ops S} {vpT : Ty S} {Γ'} (qep : ℕ)
    (s : Expr O' Γ' (cGsTy vpT)) (p bad : Expr O' Γ' .bool) :
    (cEpMgmtE 2 qep s p bad).cost = (cEpMgmtE 3 qep s p bad).cost := rfl
private theorem cSafeCh_or_cost_2_eq_3 {O' : Ops S} {vpT : Ty S} {Γ'}
    (s : Expr O' Γ' (cGsTy vpT)) (p b : Expr O' Γ' .bool) :
    (orE (.not (cSafeChE 2 s p)) b).cost = (orE (.not (cSafeChE 3 s p)) b).cost := rfl
private theorem transmitEC_cost_2_eq_3 {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L qep : ℕ) (π : Policy) {Γ'}
    (es : Expr OO Γ' (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ' (.prod .bool (.prod (.base .msg) (.opt (.base .ccoins))))) :
    (transmitEC hk L 2 qep π es arg).cost = (transmitEC hk L 3 qep π es arg).cost := by
  dsimp only [transmitEC, Comp.cost]
  with_reducible apply add_eq_both rfl
  with_reducible apply max_eq_right rfl
  with_reducible apply max_eq_right (cEpMgmtE_cost_2_eq_3 qep _ _ _)
  with_reducible apply max_eq_right rfl
  with_reducible apply add_eq_both rfl
  with_reducible apply max_eq_right rfl
  rfl
private theorem challEC_cost_2_eq_3 {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L qep : ℕ) (cfg : ConfigEC OO) (π : Policy) {Γ'}
    (es : Expr OO Γ' (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (arg : Expr OO Γ'
      (.prod .bool (.prod (.base .msg) (.prod (.base .msg) (.opt (.base .ccoins)))))) :
    (challEC hk L 2 qep cfg π es arg).cost = (challEC hk L 3 qep cfg π es arg).cost := by
  dsimp only [challEC, Comp.cost]
  with_reducible apply add_eq_both rfl
  with_reducible apply max_eq_right rfl
  with_reducible apply max_eq_right (cEpMgmtE_cost_2_eq_3 qep _ _ _)
  with_reducible apply max_eq_right (cSafeCh_or_cost_2_eq_3 _ _ _)
  with_reducible apply max_eq_right rfl
  with_reducible apply add_eq_both rfl
  with_reducible apply max_eq_right rfl
  rfl
private theorem implECDF_cost_arith
    {a b c d e f g h1 h2 i j m n p tr2 tr3 ch2 ch3 del inj2 inj3 cr2 cr3 df2 df3 k : ℕ}
    (htr : tr2 = tr3) (hch : ch2 = ch3) (hij : inj2 ≤ inj3 + k) (hcr : cr2 ≤ cr3)
    (hdf : df2 ≤ df3 + k) :
    a + (b + max ((c + (d + max (e + max (f + max
      (g + max (tr2 + h1 + 1) (ch2 + h2 + 1) + 1) (del + i + 1) + 1)
      (inj2 + j + 1) + 1) (cr2 + m + 1) + 1) + 1) + n + 1) (df2 + p + 1) + 1) + 1 ≤
    a + (b + max ((c + (d + max (e + max (f + max
      (g + max (tr3 + h1 + 1) (ch3 + h2 + 1) + 1) (del + i + 1) + 1)
      (inj3 + j + 1) + 1) (cr3 + m + 1) + 1) + 1) + n + 1) (df3 + p + 1) + 1) + 1 + k := by
  omega

theorem implECDFShiftedPaperGen_true_cost_le {ι : Type} {TSpec : OracleSpec.{0, 0} ι}
    {I' : Iface S (unifSpec + TSpec)} {γvT svT ssvT rsvT hsT : Ty S}
    (hk : HooksC OO I' γvT svT ssvT rsvT hsT) (L l qep maxSkip tStar : ℕ) (cfg : ConfigEC OO)
    (π : Policy) {Γ'} (es : Expr OO Γ'
      (esTy (@vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT) hsT))
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShiftedPaperGen true hk L l 2 qep maxSkip tStar cfg π es q).cost ≤
      (implECDFShifted hk L l 3 qep maxSkip cfg π es q).cost + (ReductionDsl.bits tStar + 81) := by
  let vpT := @vpTblTy KC Γ CCoins T I KR RSt K SS RS M E γvT svT ssvT rsvT
  let smQ := ckaSMQ KC Γ CCoins T I KR RSt K SS RS M E
  let smQDF := ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E
  let Γ0 := .prod (esTy vpT hsT) smQDF :: Γ'
  let Γ1 := .prod (esTy vpT hsT) smQ :: smQ :: Γ0
  let smQ1 := match smQ with | .sum a _ => a | t => t
  let smQ2 := match smQ1 with | .sum a _ => a | t => t
  let smQ3 := match smQ2 with | .sum a _ => a | t => t
  let trQ := match smQ3 with | .sum a _ => a | t => t
  let chQ := match smQ3 with | .sum _ b => b | t => t
  have htr0 := transmitEC_cost_2_eq_3 hk L qep π
    (Γ' := trQ :: smQ3 :: smQ2 :: smQ1 :: Γ1) (.fst .v4) .v0
  have hch0 := challEC_cost_2_eq_3 hk L qep cfg π
    (Γ' := chQ :: smQ3 :: smQ2 :: smQ1 :: Γ1) (.fst .v4) .v0
  have hij : (injectECGen true hk L 2 qep tStar cfg (.fst .v2) .v0).cost ≤ _ :=
    injectECB1_cost_le_injectEC hk L qep tStar cfg
      (Γ' := .prod .bool (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E) :: smQ1 :: Γ1)
      (.fst .v2) .v0
  have hcr := corrECShiftedPaper_cost_le hk L l π (Γ' := .bool :: Γ1) (.fst .v1) .v0
  have hdf : (deliverForgeECGen true hk L 2 qep tStar cfg (.fst .v1) .v0).cost ≤ _ :=
    deliverForgeECB1_cost_le_deliverForgeEC hk L qep tStar cfg
      (Γ' := .prod .bool (.prod (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)
        (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :: Γ0) (.fst .v1) .v0
  dsimp only [implECDFShiftedPaperGen, implECDFShifted, implECShiftedPaperGen, implECShifted,
    Comp.cost]
  with_reducible exact implECDF_cost_arith htr0 hch0 hij hcr hdf
end PaperCostDominance
end CryptoGames.SM.Engine
namespace CryptoGames.SM.Construction

open ReductionDsl OracleSpec OracleComp Engine Engine.RedPRNG CKA PRFPRNG
variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

section PaperProgTotalCostLe

variable {ckaInitA ckaInitB : KC → Γ} {ckaSend : Γ → CCoins → Γ × T × I}
  {ckaReceive : Γ → T → Γ × I} {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
  {fsInitSender : K → SS} {fsInitReceiver : K → RS}
  {fsSend : SS → Header T → M → SS × E} {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
  {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
  {lam : I} {defaultE : E} {sampKR : ProbComp KR} {sampKC : ProbComp KC}
  {sampCCoins : ProbComp CCoins} {sampI : ProbComp I} {sampK : ProbComp K}

local notation "S" => ckaSig KC Γ CCoins T I KR RSt K SS RS M E
local notation "OO" =>
  ckaOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
    fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE
local notation "II" =>
  ckaIface KC Γ CCoins T I KR RSt K SS RS M E sampKR sampKC sampCCoins sampI sampK
local notation "hkCKAC" =>
  hooksCKAC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "hkCKAShiftedC" =>
  hooksCKAShiftedC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "hkPRNGC" =>
  hooksPRNGC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)
local notation "hkFSC" =>
  hooksFSC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
    (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
    (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
    (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
    (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK)

theorem redCKAAuthDFPaperProg_totalCost_le_nonPaper (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redCKAAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).totalCost q ≤
    (redCKAAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).totalCost q := by
  unfold CostedReduction.totalCost redCKAAuthDFPaperProg redCKAAuthDFProg; dsimp only
  have h := implECDFPaper_cost_le (hkCKAC B Δcka ⟨true, tL, t⟩)
    L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy
    (Γ' := [ckaEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q (by omega)) _) _

theorem redPRNGAuthDFPaperProg_totalCost_le_nonPaper (L B Δcka qep maxSkip : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redPRNGAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).totalCost q ≤
    (redPRNGAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip tL t).totalCost q := by
  unfold CostedReduction.totalCost redPRNGAuthDFPaperProg redPRNGAuthDFProg prngOps; dsimp only
  have h := implECDFPaper_cost_le (hkPRNGC B ⟨true, tL, t⟩)
    L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy
    (Γ' := [prngEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q (by omega)) _) _

theorem redFSAuthDFPaperProg_totalCost_le_nonPaper (L B Δcka qep maxSkip j : ℕ)
    (tL : Option ℕ) (t q : ℕ) :
    (redFSAuthDFPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip j tL t).totalCost q ≤
    (redFSAuthDFProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B Δcka qep maxSkip j tL t).totalCost q := by
  unfold CostedReduction.totalCost redFSAuthDFPaperProg redFSAuthDFProg prngOps; dsimp only
  have h := implECDFPaper_cost_le (hkFSC L B Δcka ⟨true, tL, t⟩ j)
    L (2 + Δcka) qep maxSkip (modeCfgEC OO ⟨true, tL, t⟩) (⟨true, tL, t⟩ : Mode).policy
    (Γ' := [fsEsTy KC Γ CCoins T I KR RSt K SS RS M E,
      ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q (by omega)) _) _

private theorem nat_le_refl (n : ℕ) : n ≤ n := le_rfl
private theorem nat_max_le_max {a b c d : ℕ} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d := by omega

private theorem vRecvStep1C_hooksCKAShiftedC_zero_cost_le (B l t : ℕ) {Γ'}
    (h : Expr OO Γ' ckaShiftedHsTy) (ctx : Expr OO Γ' (cGsTy ckaVpTy)) (p : Expr OO Γ' .bool)
    (s : Expr OO Γ' ckaVpTy) (c : Expr OO Γ' (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E)) :
    (vRecvStep1C (hkCKAShiftedC B l 0) h ctx p s c).cost ≤
      (vRecvStep1C (hkCKAShiftedC B l t) h ctx p s c).cost := by
  unfold vRecvStep1C hooksCKAShiftedC ckaShiftedStartRecvC ckaStartRecvAnsE
  dsimp only [Comp.cost, Expr.cost, Mode.tStar]
  repeat' first
    | with_reducible apply Nat.add_le_add | with_reducible apply nat_max_le_max
    | with_reducible exact nat_le_refl _ | exact ReductionDsl.bits_mono (Nat.zero_le t)

private theorem vRecvC_hooksCKAShiftedC_zero_cost_le (B l t : ℕ) {Γ'}
    (h : Expr OO Γ' ckaShiftedHsTy) (ctx : Expr OO Γ' (cGsTy ckaVpTy)) (p : Expr OO Γ' .bool)
    (s : Expr OO Γ' ckaVpTy) (c : Expr OO Γ' (ckaHdrCtTy KC Γ CCoins T I KR RSt K SS RS M E))
    (rec_ : Expr OO Γ' (.opt (@cRecTy KC Γ CCoins T I KR RSt K SS RS M E))) :
    (vRecvC (hkCKAShiftedC B l 0) h ctx p s c rec_).cost ≤
      (vRecvC (hkCKAShiftedC B l t) h ctx p s c rec_).cost := by
  have hfr : ∀ {Γ3} hE ctxE pE tE rsvE hdrE eE recE,
      ((hkCKAShiftedC B l 0).fsRecv (Γ' := Γ3) hE ctxE pE tE rsvE hdrE eE recE).cost =
      ((hkCKAShiftedC B l t).fsRecv (Γ' := Γ3) hE ctxE pE tE rsvE hdrE eE recE).cost :=
    fun _ _ _ _ _ _ _ _ => rfl
  unfold vRecvC; dsimp only [Comp.cost, Expr.cost]; rw [hfr]
  repeat' first
    | with_reducible apply Nat.add_le_add | with_reducible apply nat_max_le_max
    | with_reducible exact nat_le_refl _
    | with_reducible apply vRecvStep1C_hooksCKAShiftedC_zero_cost_le

private theorem implECDFShifted_hooksCKAShiftedC_zero_cost_le (L B l t qep maxSkip : ℕ)
    (cfg : ConfigEC OO) (π : Policy) {Γ'} (es : Expr OO Γ' ckaShiftedEsTy)
    (q : Expr OO Γ' (ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E)) :
    (implECDFShifted (hkCKAShiftedC B l 0) L l 3 qep maxSkip cfg π es q).cost ≤
      (implECDFShifted (hkCKAShiftedC B l t) L l 3 qep maxSkip cfg π es q).cost := by
  have htr : ∀ {Γ''} (es' : Expr OO Γ'' ckaShiftedEsTy) (q' : Expr OO Γ'' _),
      (transmitEC (hkCKAShiftedC B l 0) L 3 qep π es' q').cost =
      (transmitEC (hkCKAShiftedC B l t) L 3 qep π es' q').cost := fun _ _ => rfl
  have hch : ∀ {Γ''} (es' : Expr OO Γ'' ckaShiftedEsTy) (q' : Expr OO Γ'' _),
      (challEC (hkCKAShiftedC B l 0) L 3 qep cfg π es' q').cost =
      (challEC (hkCKAShiftedC B l t) L 3 qep cfg π es' q').cost := fun _ _ => rfl
  have hcr : ∀ {Γ''} (es' : Expr OO Γ'' ckaShiftedEsTy) (p' : Expr OO Γ'' .bool),
      (corrECShifted (hkCKAShiftedC B l 0) L l π es' p').cost =
      (corrECShifted (hkCKAShiftedC B l t) L l π es' p').cost := fun _ _ => rfl
  have hcm : ∀ {Γ3} esE ctxE pE oldE newE posE,
      (commitEC (hkCKAShiftedC B l 0) L (Γ' := Γ3) esE ctxE pE oldE newE posE).cost =
      (commitEC (hkCKAShiftedC B l t) L (Γ' := Γ3) esE ctxE pE oldE newE posE).cost :=
    fun _ _ _ _ _ _ => rfl
  have hdl : ∀ {Γ''} (es' : Expr OO Γ'' ckaShiftedEsTy) (q' : Expr OO Γ'' _),
      (deliverEC (hkCKAShiftedC B l 0) L maxSkip cfg es' q').cost ≤
      (deliverEC (hkCKAShiftedC B l t) L maxSkip cfg es' q').cost := by
    intro Γ'' es' q'; unfold deliverEC; dsimp only [Comp.cost, Expr.cost]; rw [hcm]
    repeat' first
      | with_reducible apply Nat.add_le_add | with_reducible apply nat_max_le_max
      | with_reducible exact nat_le_refl _
      | with_reducible apply vRecvC_hooksCKAShiftedC_zero_cost_le
  have hij : ∀ {Γ''} (es' : Expr OO Γ'' ckaShiftedEsTy) (q' : Expr OO Γ'' _),
      (injectEC (hkCKAShiftedC B l 0) L 3 qep cfg es' q').cost ≤
      (injectEC (hkCKAShiftedC B l t) L 3 qep cfg es' q').cost := by
    intro Γ'' es' q'; unfold injectEC; dsimp only [Comp.cost, Expr.cost, orE]; rw [hcm]
    repeat' first
      | with_reducible apply Nat.add_le_add | with_reducible apply nat_max_le_max
      | with_reducible exact nat_le_refl _
      | with_reducible apply vRecvC_hooksCKAShiftedC_zero_cost_le
  have hdf : ∀ {Γ''} (es' : Expr OO Γ'' ckaShiftedEsTy) (q' : Expr OO Γ'' _),
      (deliverForgeEC (hkCKAShiftedC B l 0) L 3 qep cfg es' q').cost ≤
      (deliverForgeEC (hkCKAShiftedC B l t) L 3 qep cfg es' q').cost := by
    intro Γ'' es' q'; unfold deliverForgeEC; dsimp only [Comp.cost, Expr.cost, orE]; rw [hcm]
    repeat' first
      | with_reducible apply Nat.add_le_add | with_reducible apply nat_max_le_max
      | with_reducible exact nat_le_refl _
      | with_reducible apply vRecvC_hooksCKAShiftedC_zero_cost_le
  unfold implECDFShifted implECShifted; dsimp only [Comp.cost, Expr.cost]; rw [htr, hch, hcr]
  repeat' first
    | with_reducible apply Nat.add_le_add | with_reducible apply nat_max_le_max
    | with_reducible exact nat_le_refl _ | with_reducible apply hdl
    | with_reducible apply hij | with_reducible apply hdf

theorem redCKAAuthDFShiftedPaperProg_totalCost_le_nonPaper (L B l t qep maxSkip q : ℕ) :
    (redCKAAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip l t).totalCost q ≤
    (redCKAAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip l t).totalCost q := by
  unfold CostedReduction.totalCost redCKAAuthDFShiftedPaperProg redCKAAuthDFShiftedPaperGenProg
    redCKAAuthDFShiftedProg
  have hd : decide (1 = 0) = false := rfl
  have h := implECDFShiftedPaper_cost_le (hkCKAShiftedC B l t)
    L l 3 qep maxSkip t (modeCfgEC OO ⟨true, some (l - 1), t⟩)
    (⟨true, some (l - 1), t⟩ : Mode).policy
    (Γ' := [ckaShiftedEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  dsimp only [Nat.reduceAdd] at h ⊢; rw [hd]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q (by omega)) _) _

theorem redCKAAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper (L B l t qep maxSkip q : ℕ) :
    (redCKAAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip l t).totalCost q ≤
    (redCKAAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip l t).totalCost q + q * (ReductionDsl.bits t + 81) := by
  let mo : Mode := ⟨true, some (l - 1), t⟩
  let Γc := [ckaShiftedEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]
  unfold CostedReduction.totalCost redCKAAuthDFShiftedDir2PaperProg redCKAAuthDFShiftedPaperGenProg
    redCKAAuthDFShiftedProg; dsimp only [Comp.cost, Expr.cost, Nat.reduceAdd]
  have hd : decide (0 = 0) = true := rfl
  have h1 := implECDFShiftedPaperGen_true_cost_le (hkCKAShiftedC B l 0)
    L l qep maxSkip t (modeCfgEC OO mo) mo.policy (Γ' := Γc) .v0 .v1
  have h2 := implECDFShifted_hooksCKAShiftedC_zero_cost_le
    (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
    (sampI := sampI) (sampK := sampK) L B l t qep maxSkip (modeCfgEC OO mo) mo.policy
    (Γ' := Γc) .v0 .v1
  have hout : (authOutE (O' := OO) L 2 mo.policy (Γ' := [ckaShiftedEsTy, .bool]) .v0).cost =
      (authOutE (O' := OO) L 3 mo.policy (Γ' := [ckaShiftedEsTy, .bool]) .v0).cost := rfl
  have hmul : q * max 1 ((implECDFShiftedPaperGen true (hkCKAShiftedC B l 0) L l 2 qep maxSkip t
        (modeCfgEC OO mo) mo.policy (Γ' := Γc) .v0 .v1).cost + 13) ≤
      q * max 1 ((implECDFShifted (hkCKAShiftedC B l t) L l 3 qep maxSkip
        (modeCfgEC OO mo) mo.policy (Γ' := Γc) .v0 .v1).cost + 13) + q * (ReductionDsl.bits t + 81) := by
    rw [← Nat.left_distrib]; exact Nat.mul_le_mul_left q (by omega)
  dsimp only [mo, Γc] at hout hmul; rw [hd, hout]; omega

theorem redPRNGAuthDFShiftedPaperProg_totalCost_le_nonPaper (L B l t qep maxSkip q : ℕ) :
    (redPRNGAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip l t).totalCost q ≤
    (redPRNGAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip l t).totalCost q := by
  unfold CostedReduction.totalCost redPRNGAuthDFShiftedPaperProg redPRNGAuthDFShiftedPaperGenProg
    redPRNGAuthDFShiftedProg prngOps
  have hd : (!true) = false := rfl
  have h := implECDFShiftedPaper_cost_le (hkPRNGC B ⟨true, some (l - 1), t⟩)
    L l 3 qep maxSkip t (modeCfgEC OO ⟨true, some (l - 1), t⟩)
    (⟨true, some (l - 1), t⟩ : Mode).policy
    (Γ' := [prngEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  dsimp only [Nat.reduceAdd] at h ⊢; rw [hd]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q (by omega)) _) _

theorem redPRNGAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper (L B l t qep maxSkip q : ℕ) :
    (redPRNGAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip l t).totalCost q ≤
    (redPRNGAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip l t).totalCost q + q * (ReductionDsl.bits t + 81) := by
  let moF : Mode := ⟨false, some (l - 1), t⟩
  let moT : Mode := ⟨true, some (l - 1), t⟩
  let Γp := [prngEsTy, ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]
  unfold CostedReduction.totalCost redPRNGAuthDFShiftedDir2PaperProg redPRNGAuthDFShiftedPaperGenProg
    redPRNGAuthDFShiftedProg prngOps; dsimp only [Comp.cost, Expr.cost, Nat.reduceAdd]
  have hd : (!false) = true := rfl
  have himpl : (implECDFShifted (hkPRNGC B moF) L l 3 qep maxSkip
      (modeCfgEC OO moT) moT.policy (Γ' := Γp) .v0 .v1).cost =
    (implECDFShifted (hkPRNGC B moT) L l 3 qep maxSkip
      (modeCfgEC OO moT) moT.policy (Γ' := Γp) .v0 .v1).cost := rfl
  have h1 := implECDFShiftedPaperGen_true_cost_le (hkPRNGC B moF)
    L l qep maxSkip t (modeCfgEC OO moT) moT.policy (Γ' := Γp) .v0 .v1
  rw [himpl] at h1
  have hout : (authOutE (O' := OO) L 2 moT.policy (Γ' := [prngEsTy, .bool]) .v0).cost =
      (authOutE (O' := OO) L 3 moT.policy (Γ' := [prngEsTy, .bool]) .v0).cost := rfl
  have hmul : q * max 1 ((implECDFShiftedPaperGen true (hkPRNGC B moF) L l 2 qep maxSkip t
        (modeCfgEC OO moT) moT.policy (Γ' := Γp) .v0 .v1).cost + 13) ≤
      q * max 1 ((implECDFShifted (hkPRNGC B moT) L l 3 qep maxSkip
        (modeCfgEC OO moT) moT.policy (Γ' := Γp) .v0 .v1).cost + 13) + q * (ReductionDsl.bits t + 81) := by
    rw [← Nat.left_distrib]; exact Nat.mul_le_mul_left q (by omega)
  have hinit : (initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) moF (Γ' := [.unit]) (.bool false)).cost =
    (initPRNGEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) moT (Γ' := [.unit]) (.bool false)).cost := rfl
  dsimp only [moF, moT, Γp] at hinit hout hmul; rw [hd, hinit, hout]; omega

theorem redFSAuthDFShiftedPaperProg_totalCost_le_nonPaper (L B j l t qep maxSkip q : ℕ) :
    (redFSAuthDFShiftedPaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip j l t).totalCost q ≤
    (redFSAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip j l t).totalCost q := by
  unfold CostedReduction.totalCost redFSAuthDFShiftedPaperProg redFSAuthDFShiftedPaperGenProg
    redFSAuthDFShiftedProg prngOps
  have hd : (!true) = false := rfl
  have h := implECDFShiftedPaper_cost_le (hkFSC L B 1 ⟨true, some (l - 1), t⟩ j)
    L l 3 qep maxSkip t (modeCfgEC OO ⟨true, some (l - 1), t⟩)
    (⟨true, some (l - 1), t⟩ : Mode).policy
    (Γ' := [fsEsTy KC Γ CCoins T I KR RSt K SS RS M E,
      ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]) .v0 .v1
  dsimp only [Nat.reduceAdd] at h ⊢; rw [hd]
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left q (by omega)) _) _

theorem redFSAuthDFShiftedDir2PaperProg_totalCost_le_nonPaper (L B j l t qep maxSkip q : ℕ) :
    (redFSAuthDFShiftedDir2PaperProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB)
      (ckaSend := ckaSend) (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B qep maxSkip j l t).totalCost q ≤
    (redFSAuthDFShiftedProg (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L B 1 qep maxSkip j l t).totalCost q + q * (ReductionDsl.bits t + 81) := by
  let moF : Mode := ⟨false, some (l - 1), t⟩
  let moT : Mode := ⟨true, some (l - 1), t⟩
  let hk0 := hkFSC L B 0 moF j
  let hk1 := hkFSC L B 1 moT j
  let Γf := [fsEsTy KC Γ CCoins T I KR RSt K SS RS M E,
    ckaSMQDF KC Γ CCoins T I KR RSt K SS RS M E]
  have hd : (!false) = true := rfl
  have hsc : ∀ {O' : Ops S} {Γ''}
      (sE : Expr O' Γ'' (cGsTy (fsVpTy KC Γ CCoins T I KR RSt K SS RS M E))) pE,
      (cSafeChE 2 sE pE).cost = (cSafeChE 3 sE pE).cost := fun _ _ => rfl
  have hvs : ∀ {Γ''} hE ctxE pE sE mE pairE cE,
      (vSendC hk0 (Γ' := Γ'') hE ctxE pE sE mE pairE cE).cost =
      (vSendC hk1 (Γ' := Γ'') hE ctxE pE sE mE pairE cE).cost := by
    intros; unfold vSendC vSendStep1C hk0 hk1 hooksFSC fsStartSendC fsFsSendC rootFSC
    dsimp only [Comp.cost, Expr.cost, Mode.tH, Nat.reduceAdd]; rw [hsc]
  have hvr1 : ∀ {Γ''} hE ctxE pE sE cE,
      (vRecvStep1C hk0 (Γ' := Γ'') hE ctxE pE sE cE).cost =
      (vRecvStep1C hk1 (Γ' := Γ'') hE ctxE pE sE cE).cost := by
    intros; unfold vRecvStep1C hk0 hk1 hooksFSC fsStartRecvC; dsimp only [Comp.cost, Expr.cost]
  have hfr : ∀ {Γ''} hE ctxE pE tE rsvE hdrE eE recE,
      (hk0.fsRecv (Γ' := Γ'') hE ctxE pE tE rsvE hdrE eE recE).cost =
      (hk1.fsRecv (Γ' := Γ'') hE ctxE pE tE rsvE hdrE eE recE).cost := fun _ _ _ _ _ _ _ _ => rfl
  have hvr : ∀ {Γ''} hE ctxE pE sE cE recE,
      (vRecvC hk0 (Γ' := Γ'') hE ctxE pE sE cE recE).cost =
      (vRecvC hk1 (Γ' := Γ'') hE ctxE pE sE cE recE).cost := by
    intros; unfold vRecvC; dsimp only [Comp.cost, Expr.cost]; rw [hvr1, hfr]
  have hcr : ∀ {Γ''} π esE pE,
      (corrECShifted hk0 L l π (Γ' := Γ'') esE pE).cost =
      (corrECShifted hk1 L l π (Γ' := Γ'') esE pE).cost := by
    intros; unfold corrECShifted hk0 hk1 hooksFSC fsRevealC; dsimp only [Comp.cost, Expr.cost]
  have hinit : (initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L moF j (Γ' := [.unit]) (.bool false)).cost =
    (initFSEStateC (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver) (fsSend := fsSend)
      (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI) (eqM := eqM) (eqE := eqE) (lam := lam)
      (defaultE := defaultE) (sampKR := sampKR) (sampKC := sampKC) (sampCCoins := sampCCoins)
      (sampI := sampI) (sampK := sampK) L moT j (Γ' := [.unit]) (.bool false)).cost := rfl
  have hcm : ∀ {Γ''} esE ctxE pE oldE newE posE,
      (commitEC hk0 L (Γ' := Γ'') esE ctxE pE oldE newE posE).cost =
      (commitEC hk1 L (Γ' := Γ'') esE ctxE pE oldE newE posE).cost := fun _ _ _ _ _ _ => rfl
  have htr : ∀ {Γ''} π esE qE,
      (transmitEC hk0 L 3 qep π (Γ' := Γ'') esE qE).cost =
      (transmitEC hk1 L 3 qep π (Γ' := Γ'') esE qE).cost := by
    intros; unfold transmitEC; dsimp only [Comp.cost, Expr.cost, esMk]; rw [hvs]
  have hch : ∀ {Γ''} cfg π esE qE,
      (challEC hk0 L 3 qep cfg π (Γ' := Γ'') esE qE).cost =
      (challEC hk1 L 3 qep cfg π (Γ' := Γ'') esE qE).cost := by
    intros; unfold challEC; dsimp only [Comp.cost, Expr.cost, esMk, orE]; rw [hvs]
  have hdl : ∀ {Γ''} cfg esE qE,
      (deliverEC hk0 L maxSkip cfg (Γ' := Γ'') esE qE).cost =
      (deliverEC hk1 L maxSkip cfg (Γ' := Γ'') esE qE).cost := by
    intros; unfold deliverEC; dsimp only [Comp.cost, Expr.cost]; rw [hvr, hcm]
  have hij : ∀ {Γ''} cfg esE qE,
      (injectEC hk0 L 3 qep cfg (Γ' := Γ'') esE qE).cost =
      (injectEC hk1 L 3 qep cfg (Γ' := Γ'') esE qE).cost := by
    intros; unfold injectEC; dsimp only [Comp.cost, Expr.cost, orE]; rw [hvr, hcm]
  have hdf : ∀ {Γ''} cfg esE qE,
      (deliverForgeEC hk0 L 3 qep cfg (Γ' := Γ'') esE qE).cost =
      (deliverForgeEC hk1 L 3 qep cfg (Γ' := Γ'') esE qE).cost := by
    intros; unfold deliverForgeEC; dsimp only [Comp.cost, Expr.cost, orE]; rw [hvr, hcm]
  have himpl : ∀ {Γ''} cfg π esE qE,
      (implECDFShifted hk0 L l 3 qep maxSkip cfg π (Γ' := Γ'') esE qE).cost =
      (implECDFShifted hk1 L l 3 qep maxSkip cfg π (Γ' := Γ'') esE qE).cost := by
    intros; unfold implECDFShifted implECShifted; dsimp only [Comp.cost, Expr.cost]
    rw [htr, hch, hdl, hij, hcr, hdf]
  have h1 := implECDFShiftedPaperGen_true_cost_le hk0
    L l qep maxSkip t (modeCfgEC OO moT) moT.policy (Γ' := Γf) .v0 .v1
  rw [himpl] at h1
  have hmul : q * max 1 ((implECDFShiftedPaperGen true hk0
        L l 2 qep maxSkip t (modeCfgEC OO moT) moT.policy (Γ' := Γf) .v0 .v1).cost + 13) ≤
      q * max 1 ((implECDFShifted hk1 L l 3 qep maxSkip
        (modeCfgEC OO moT) moT.policy (Γ' := Γf) .v0 .v1).cost + 13) + q * (ReductionDsl.bits t + 81) := by
    rw [← Nat.left_distrib]; exact Nat.mul_le_mul_left q (by omega)
  unfold CostedReduction.totalCost redFSAuthDFShiftedDir2PaperProg redFSAuthDFShiftedPaperGenProg
    redFSAuthDFShiftedProg prngOps
  dsimp only [Comp.cost, Expr.cost, Nat.reduceAdd, hk0, hk1, moF, moT, Γf] at hinit hmul ⊢
  rw [hd, hinit]; omega
end PaperProgTotalCostLe
end CryptoGames.SM.Construction
