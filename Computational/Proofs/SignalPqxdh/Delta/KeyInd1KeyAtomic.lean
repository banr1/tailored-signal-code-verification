/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Headline
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeySigWire
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyShcr
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDhWire
import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKemBounds

/-!
# Atomic-signature one-key PQXDH `KeyInd` reductions and bounds

Lifts the three one-key `KeyInd` `ReductionDsl` programs (`sigKeyInd1KeyDslProg`,
`shcrKeyInd1KeyDslProg`, and `fgKeyInd1KeyGapDhDslProg`) from `pqxdhOps` onto the shared
`pqAtomicOps` and `pqAtomicSamplers` tables via `AtomicLift`, proving their syntactic step-cost,
query-count, and output block-size bounds, semantic `.Bounded` query compliance, and game-advantage
transfer theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace Proofs.SignalPqxdh.Security.PqxdhDelta

/-! ## Unsupported-query vanishing -/

section OneKeyUnsupported

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open _root_.Proofs.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift

private def zSigDdhW : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag → ℕ :=
  tlSigDdhKeyInd.unsupportedW

private def zSigDdhWS : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.smp.Samp → ℕ :=
  fun _ => 0

@[simp] private theorem s1Prim_unsupported {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (s1Prim c).queries zSigDdhW zSigDdhWS =
      c.queries keyIndUnsupportedPrimW zPrimWS := by
  unfold s1Prim
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[simp] private theorem qSigDdhSign_unsupported (m : ℕ+)
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (msg : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) :
    (qSigDdhSign m msg).queries zSigDdhW zSigDdhWS = 0 := rfl

@[simp] private theorem sigChalQ_dsl_unsupported (m : ℕ+)
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (msg : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) :
    (sigChalQ_dsl m msg).queries zSigDdhW zSigDdhWS = 0 := rfl

@[simp] private theorem liftGdhToSigDdh_unsupported
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries zSigDdhW zSigDdhWS =
      c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[simp] private theorem liftGdhComp_unsupported
    {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhComp c).queries zSigDdhW zSigDdhWS =
      c.queries zGapDhW zGapDhWS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

theorem sigKeyInd1KeyProg_init_unsupported (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sigKeyInd1KeyProg S K).init.queries zSigDdhW zSigDdhWS = 0
  simp [sigKeyInd1KeyProg, bindV, Comp.queries]

theorem sigKeyInd1KeyProg_finish_unsupported (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := rfl

theorem shcrKeyInd1KeyProg_init_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyInd1KeyProg S Q K).init.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcrKeyIndProg_init_unsupported S Q K

theorem shcrKeyInd1KeyProg_chDone_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyInd1KeyProg S Q K).chDone.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcrKeyIndProg_chDone_unsupported S Q K

theorem shcrKeyInd1KeyProg_resume_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyInd1KeyProg S Q K).resume.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcrKeyIndProg_resume_unsupported S Q K

theorem shcrKeyInd1KeyProg_finish_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyInd1KeyProg S Q K).finish.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 :=
  shcrKeyIndProg_finish_unsupported S Q K

private theorem initPrin1KeyB_prim_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrin1KeyB (Δ := Δ) K st u).queries
      keyIndUnsupportedPrimW zPrimWS = 0 := by
  simp [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrin1KeyB, bindV, Comp.queries]

theorem shcrKeyInd1KeyProg_handlePost_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyInd1KeyProg S Q K).handlePost.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have h2 := shcrKeyIndProg_handlePost_unsupported S Q K
  dsimp only [shcrKeyIndProg, shcrKeyInd1KeyProg, SignalPqxdh.LegacyCosted.keyIndCodec] at h2 ⊢
  change (shcrPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0 at h2
  change (shcr1KeyPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0
  rw [shcrPostC_eq_tail] at h2
  unfold shcr1KeyPostC
  simp only [caseSumV, onBase, letV, bindV, initPrin1KeyB_prim_unsupported, Comp.queries] at h2 ⊢
  omega

theorem shcrKeyInd1KeyProg_handlePre_unsupported (S : Setup) (Q K : Nat) :
    (shcrKeyInd1KeyProg S Q K).handlePre.queries tlPrimKeyInd.unsupportedW (fun _ => 0) = 0 := by
  have h2 := shcrKeyIndProg_handlePre_unsupported S Q K
  dsimp only [shcrKeyIndProg, shcrKeyInd1KeyProg, SignalPqxdh.LegacyCosted.keyIndCodec] at h2 ⊢
  change (shcrPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0 at h2
  change (shcr1KeyPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries keyIndUnsupportedPrimW zPrimWS = 0
  unfold shcrPreC at h2
  unfold shcr1KeyPreC
  rw [shcrPostC_eq_tail] at h2
  unfold shcr1KeyPostC
  simp only [letV, bindV, caseOptV, caseSumV, onBase, initPrin1KeyB_prim_unsupported,
    Comp.queries] at h2 ⊢
  omega

theorem fgKeyInd1KeyGapDhProg_init_unsupported (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (fgKeyInd1KeyGapDhProg S K).init.queries zSigDdhW zSigDdhWS = 0
  simp [fgKeyInd1KeyGapDhProg, initAdv4_1Key, initAdv4_1KeyBase,
    letV, bindV, Comp.queries]

theorem fgKeyInd1KeyGapDhProg_handle_unsupported (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyHandle S K).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (gdhHandle S K).queries zGapDhW zGapDhWS = 0 := gdhHandle_unsupported S K
  simp [gdh1KeyHandle,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh.initPrin1KeyB,
    genSpk1KeyB, callGdhHandle, hGdh,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

theorem fgKeyInd1KeyGapDhProg_finish_unsupported (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDhProg S K).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyFinish S K).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (gdhFinish S K).queries zGapDhW zGapDhWS = 0 := gdhFinish_unsupported S K
  simp [gdh1KeyFinish, hGdh, letV, Comp.queries]

@[simp] private theorem wrapBase2_unsupported
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries zGapDhW zGapDhWS =
      c.queries keyIndUnsupportedPrimW zPrimWS := by
  simp [wrapBase2, bindV, Comp.queries]

@[simp] private theorem wrapSim2_unsupported
    {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Δ
      (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries zGapDhW zGapDhWS =
      c.queries zGapDhW zGapDhWS := by
  simp [wrapSim2, bindV, Comp.queries]

@[simp] private theorem roRawFallbackC_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (SignalPqxdh.LegacyCosted.B 192)) :
    (roRawFallbackC (Δ := Δ) K sm sec).queries zGapDhW zGapDhWS = 0 := by
  simp [roRawFallbackC, bindV, caseOptV, Comp.queries]

@[simp] private theorem roParsedC_unsupported (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (SignalPqxdh.LegacyCosted.B 192)) :
    (roParsedC (Δ := Δ) K sm sec).queries zGapDhW zGapDhWS = 0 := by
  simp [roParsedC, letV, bindV, Comp.queries]

@[simp] private theorem initPrinGdh2B_unsupported (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) :
    (initPrinGdh2B (Δ := Δ) K pa sm bSt u).queries zGapDhW zGapDhWS = 0 := by
  simp [initPrinGdh2B, letV, bindV, Comp.queries]

@[simp] private theorem genSpkGdh2B_unsupported (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    (genSpkGdh2B (Δ := Δ) K pa sm bSt x).queries zGapDhW zGapDhWS = 0 := by
  simp [genSpkGdh2B, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem genOpkGdh2B_unsupported (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) :
    (genOpkGdh2B (Δ := Δ) K pa sm bSt x).queries zGapDhW zGapDhWS = 0 := by
  simp [genOpkGdh2B, letV, bindV, Comp.queries]

@[simp] private theorem initiateGdh2B_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    (initiateGdh2B (Δ := Δ) S K pa sm bSt hasOpk x).queries zGapDhW zGapDhWS = 0 := by
  simp [initiateGdh2B, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem finishAcceptGdhC_unsupported (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.opt (SignalPqxdh.LegacyCosted.B 32)))
    (opks' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod .nat (.prod SignalPqxdh.LegacyCosted.U32
        (.prod SignalPqxdh.LegacyCosted.U32 (SignalPqxdh.LegacyCosted.B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    (finishAcceptGdhC (Δ := Δ) S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).queries
      zGapDhW zGapDhWS = 0 := by
  simp [finishAcceptGdhC, letV, bindV, Comp.queries]

@[simp] private theorem acceptOpkGdh2B_unsupported (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    (acceptOpkGdh2B (Δ := Δ) S K pa sm bSt x).queries zGapDhW zGapDhWS = 0 := by
  simp [acceptOpkGdh2B, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem acceptNoOpkGdhB_unsupported (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    (acceptNoOpkGdhB (Δ := Δ) S K sm bSt x).queries zGapDhW zGapDhWS = 0 := by
  simp [acceptNoOpkGdhB, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem registerGdhB_unsupported
    {Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (sk : Var Γ₄ (SignalPqxdh.LegacyCosted.B 32)) :
    (registerGdhB (Δ := Δ) sm bSt sk).queries zGapDhW zGapDhWS = 0 := by
  simp [registerGdhB, bindV, Comp.queries]

private theorem gdhHandle2_unsupported (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries zGapDhW zGapDhWS = 0 := by
  simp [gdhHandle2, corruptB, testB, revealB, revealSpkB,
    letV, caseOptV, caseSumV, Comp.queries]

private theorem gdhFinish2_unsupported (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queries zGapDhW zGapDhWS = 0 := by
  simp [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, Comp.queries]

private theorem bernoulliRatioGdhC_unsupported {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries zGapDhW zGapDhWS = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [bindV, Comp.queries]

private theorem chooseArm2C_unsupported {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT} (A B : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries zGapDhW zGapDhWS = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) A B c1 c2).queries zGapDhW zGapDhWS = 0 := by
  unfold chooseArm2C
  split_ifs <;> simp [bindV, Comp.queries, bernoulliRatioGdhC_unsupported, h1, h2]

private theorem initParams1Key2C_unsupported (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))) :
    (initParams1Key2C S (Δ := Δ) uv).queries zGapDhW zGapDhWS = 0 := by
  have hp : ∀ {Δ' : List PT}, (samplePrin2C S (Δ := Δ')).queries zGapDhW zGapDhWS = 0 := by
    intro Δ'; unfold samplePrin2C; split_ifs <;> simp [bindV, Comp.queries]
  have hs : ∀ {Δ' : List PT}, (sampleSpkPair2C S (Δ := Δ')).queries zGapDhW zGapDhWS = 0 := by
    intro Δ'; unfold sampleSpkPair2C; split_ifs <;> simp [bindV, Comp.queries]
  have ho : ∀ {Δ' : List PT}, (sampleOpkTriple2C S (Δ := Δ')).queries zGapDhW zGapDhWS = 0 := by
    intro Δ'; unfold sampleOpkTriple2C; split_ifs <;> simp [bindV, Comp.queries]
  have hso : ∀ {Δ' : List PT}, (sampleSendOpkTarget2C S (Δ := Δ')).queries zGapDhW zGapDhWS = 0 := by
    intro Δ'; unfold sampleSendOpkTarget2C; split_ifs <;> simp [bindV, Comp.queries]
  have hsno : ∀ {Δ' : List PT}, (sampleSendNoOpkTarget2C S (Δ := Δ')).queries zGapDhW zGapDhWS = 0 := by
    intro Δ'; unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [bindV, Comp.queries]
  have hst : ∀ {Δ' : List PT}, (sampleSendTarget2C S (Δ := Δ')).queries zGapDhW zGapDhWS = 0 := by
    intro Δ'; unfold sampleSendTarget2C
    split_ifs
    · rfl
    · exact chooseArm2C_unsupported (Γ₁ := Δ') _ _ _ _ hso hsno
  unfold initParams1Key2C
  split_ifs
  · rfl
  · refine chooseArm2C_unsupported _ _ _ _ ?_ ?_
    · intro Δ' _; refine chooseArm2C_unsupported _ _ _ _ ?_ ?_ <;>
        (intro Δ'' _; simp [bindV, Comp.queries, hp, hs, hst])
    · intro Δ' _; refine chooseArm2C_unsupported _ _ _ _ ?_ ?_ <;>
        (intro Δ'' _; simp [bindV, Comp.queries, hp, hst, hso, ho])

private theorem fgKeyInd1KeyGapDh2Prog_init_unsupported (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).init.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (fgKeyInd1KeyGapDh2Prog S K).init.queries zSigDdhW zSigDdhWS = 0
  simp [fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, initAdv4_1Key2Base,
    initParams1Key2C_unsupported, letV, bindV, Comp.queries]

private theorem fgKeyInd1KeyGapDh2Prog_handle_unsupported (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyHandle2 S K).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (gdhHandle2 S K).queries zGapDhW zGapDhWS = 0 := gdhHandle2_unsupported S K
  simp [gdh1KeyHandle2, initPrin1Key2B, genSpk1Key2B, callGdhHandle2, hGdh,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

private theorem fgKeyInd1KeyGapDh2Prog_finish_unsupported (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).finish.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (gdh1KeyFinish2 S K).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (gdhFinish2 S K).queries zGapDhW zGapDhWS = 0 := gdhFinish2_unsupported S K
  simp [gdh1KeyFinish2, hGdh, letV, Comp.queries]

theorem sigKeyInd1KeyProg_handle_unsupported (S : Setup) (K : Nat) :
    (sigKeyInd1KeyProg S K).handle.queries tlSigDdhKeyInd.unsupportedW (fun _ => 0) = 0 := by
  change (sig1KeyHandleC S K).queries zSigDdhW zSigDdhWS = 0
  have hGdh : (gdhHandle2 S K).queries zGapDhW zGapDhWS = 0 := gdhHandle2_unsupported S K
  simp [sig1KeyHandleC, sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyInitiateCheckC, extract1KeyC, delegateFgC, hGdh,
    letV, bindV, caseOptV, caseSumV, Comp.queries]

end OneKeyUnsupported

/-! ## 64-byte sample count bound -/

section Sig1KeyR64

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open Computational.Proofs.SignalPqxdh.AtomicLift

private def zPrim0W : SignalPqxdh.LegacyCosted.pqPrimIface.Tag → ℕ := fun _ => 0
private def zGdh0W : SignalPqxdh.LegacyCosted.pqGapDhIface.Tag → ℕ := fun _ => 0
private def zSigDdh0W : SignalPqxdh.LegacyCosted.pqSigAndDdhIface.Tag → ℕ := fun _ => 0
private def kiR64WS : SignalPqxdh.LegacyCosted.PSamp → ℕ := r64W

@[simp] private theorem sBool_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sBool (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem sBytes32_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sBytes32 (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem sRandom64_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sRandom64 (Γ := Γ)).queries zPrim0W kiR64WS = 1 := rfl
@[simp] private theorem sDrKey96_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sDrKey96 (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem sIndex_r64 (N : ℕ) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} :
    (sIndex N (Γ := Γ)).queries zPrim0W kiR64WS = 0 := rfl

@[simp] private theorem qX25519_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))) :
    (qX25519 e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qX25519Base_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qX25519Base e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qPow8_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qPow8 e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qIsCanonical_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qIsCanonical e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qSigPkGen_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (qSigPkGen e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qSigSign_r64 (m : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 32)
        (.prod (SignalPqxdh.LegacyCosted.B m) (SignalPqxdh.LegacyCosted.B 64)))) :
    (qSigSign m e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qSigVerify_r64 (m : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 32)
        (.prod (SignalPqxdh.LegacyCosted.B m) (SignalPqxdh.LegacyCosted.B 64)))) :
    (qSigVerify m e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qKemKeyGen_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 64)) :
    (qKemKeyGen e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qKemEncaps_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 1568) (SignalPqxdh.LegacyCosted.B 32))) :
    (qKemEncaps e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qKemDecaps_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.prod (SignalPqxdh.LegacyCosted.B 3168) (SignalPqxdh.LegacyCosted.B 1568))) :
    (qKemDecaps e).queries zPrim0W kiR64WS = 0 := rfl
@[simp] private theorem qHkdfDerive96_r64 (w : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (e : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B w)) :
    (qHkdfDerive96 w e).queries zPrim0W kiR64WS = 0 := rfl

@[simp] private theorem gPrim_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (gPrim c).queries zGdh0W kiR64WS = c.queries zPrim0W kiR64WS := by
  unfold gPrim
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[simp] private theorem s1Prim_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Γ t) :
    (s1Prim c).queries zSigDdh0W kiR64WS = c.queries zPrim0W kiR64WS := by
  unfold s1Prim
  induction c with
  | query _ _ => rfl
  | sample _ _ => rfl
  | _ => simp_all [liftBase, Comp.queries]

@[simp] private theorem liftGdhToSigDdh_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).queries zSigDdh0W kiR64WS = c.queries zGdh0W kiR64WS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.queries]

@[simp] private theorem ddhQ_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (x y z : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (ddhQ x y z).queries zGdh0W kiR64WS = 0 := rfl

@[simp] private theorem qSigDdhSign_r64 (m : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (msg : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) :
    (qSigDdhSign m msg).queries zSigDdh0W kiR64WS = 0 := rfl

@[simp] private theorem findHonestC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (findHonestC S K st ik).queries zPrim0W kiR64WS = 0 := by
  simp [findHonestC, letV, findMV, bindV, Comp.queries]

@[simp] private theorem isAdvRegC_r64 (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isAdvRegC K st pk).queries zPrim0W kiR64WS = 0 := by
  simp [isAdvRegC, bindV, Comp.queries]

@[simp] private theorem isGameSpkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameSpkC S K st pk).queries zPrim0W kiR64WS = 0 := by
  simp [isGameSpkC, letV, anyMV, bindV, Comp.queries]

@[simp] private theorem isGameOpkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (pk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (isGameOpkC S K st pk).queries zPrim0W kiR64WS = 0 := by
  simp [isGameOpkC, letV, anyMV, bindV, Comp.queries]

@[simp] private theorem resolveSigPkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (resolveSigPkC S K st ik).queries zPrim0W kiR64WS = 0 := by
  simp [resolveSigPkC, letV, bindV, Comp.queries]

@[simp] private theorem honestPeerC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (honestPeerC S K st ik).queries zPrim0W kiR64WS = 0 := by
  simp [honestPeerC, bindV, Comp.queries]

@[simp] private theorem checkProvC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkProvC (Δ := Δ) S K st bu).queries zPrim0W kiR64WS = 0 := by
  simp [checkProvC, bindV, letV, caseOptV, anyMV, Comp.queries]

@[simp] private theorem partnerC_r64 {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ keyIndSessionEntryTy) (r : Var Γ₂ keyIndRespEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (partnerC (Δ := Δ) s r).queries zPrim0W kiR64WS = 0 := rfl

@[simp] private theorem koskSenderOkPowsC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (koskSenderOkPowsC S K st pows ik).queries zPrim0W kiR64WS = 0 := by
  simp [koskSenderOkPowsC, letV, bindV, Comp.queries]

@[simp] private theorem koskBundleOkPowsC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (st : Var Γ₁ keyIndStateTy)
    (pows : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (bu : Var Γ₂ preKeyBundleTy) :
    (koskBundleOkPowsC S K st pows bu).queries zPrim0W kiR64WS = 0 := by
  simp [koskBundleOkPowsC, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem lookupSpkSkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ Δ] (st : Var Γ keyIndStateTy)
    (pows : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))))
    (spkPk : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (lookupSpkSkC S K st pows spkPk).queries zPrim0W kiR64WS = 0 := by
  simp [lookupSpkSkC, letV, bindV, findMV, Comp.queries]

@[simp] private theorem chooseRespRandC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (r : Var Δ keyIndRespEntryTy) :
    (chooseRespRandC S K st r).queries zGdh0W kiR64WS = 0 := by
  simp [chooseRespRandC, bindV, caseOptV, findMV, Comp.queries]

@[simp] private theorem chooseInitRandC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ Δ]
    (st : Var Γ keyIndStateTy) (s : Var Δ keyIndSessionEntryTy) :
    (chooseInitRandC S K st s).queries zGdh0W kiR64WS = 0 := by
  simp [chooseInitRandC, bindV, caseOptV, findMV, Comp.queries]

@[simp] private theorem mkSecretPosC_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (z : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (mkSecretPosC z).queries zGdh0W kiR64WS = 0 := by
  simp [mkSecretPosC, letV, bindV, Comp.queries]

@[simp] private theorem mkPairPosC_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (pk1 pk2 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (mkPairPosC pk1 pk2).queries zGdh0W kiR64WS = 0 := by
  simp [mkPairPosC, letV, bindV, Comp.queries]

@[simp] private theorem computePosC_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (sk1 sk2 pk1 pk2 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32)) :
    (computePosC sk1 sk2 pk1 pk2).queries zGdh0W kiR64WS = 0 := by
  simp [computePosC, bindV, Comp.queries]

@[simp] private theorem computeOptPosInitC_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (sk1 pk1 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B 32))
    (opkB? : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ
      (.opt (.prod SignalPqxdh.LegacyCosted.U32 (SignalPqxdh.LegacyCosted.B 32)))) :
    (computeOptPosInitC sk1 pk1 opkB?).queries zGdh0W kiR64WS = 0 := by
  simp [computeOptPosInitC, letV, caseOptV, bindV, Comp.queries]

@[simp] private theorem ddhEqC_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (p1 p2 : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ fgPosTy) :
    (ddhEqC p1 p2).queries zGdh0W kiR64WS = 0 := by
  simp [ddhEqC, letV, caseSumV, Comp.queries]

@[simp] private theorem ddhEqOptC_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (p1? p2? : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (.opt fgPosTy)) :
    (ddhEqOptC p1? p2?).queries zGdh0W kiR64WS = 0 := by
  simp [ddhEqOptC, letV, caseOptV, Comp.queries]

@[simp] private theorem entryMatchesC_r64
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (e : Var Δ fgPatchEntryTy) :
    (entryMatchesC pos1 pos2 pos3 pos4? ss e).queries zGdh0W kiR64WS = 0 := by
  simp [entryMatchesC, bindV, Comp.queries]

@[simp] private theorem fgPatchC_r64 (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ]
    (pos1 : Var Γ₁ fgPosTy) (pos2 : Var Γ₂ fgPosTy) (pos3 : Var Γ₃ fgPosTy)
    (pos4? : Var Γ₄ (.opt fgPosTy)) (ss : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (fgL : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.list fgPatchEntryTy)) :
    (fgPatchC K pos1 pos2 pos3 pos4? ss fgL).queries zGdh0W kiR64WS = 0 := by
  simp [fgPatchC, letV, bindV, findMV, caseOptV, Comp.queries]

@[simp] private theorem comp_rename_queries_gdh :
    ∀ {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
      {t : Ty SignalPqxdh.LegacyCosted.pqSig}
      (f : ∀ {τ}, Var Γ τ → Var Δ τ)
      (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Γ t),
      (Comp.rename f c).queries zGdh0W kiR64WS = c.queries zGdh0W kiR64WS
  | _, _, _, _, .ret _ | _, _, _, _, .sample _ _ | _, _, _, _, .query _ _ => rfl
  | _, _, _, f, .bind c k => by
    simp [Comp.rename, Comp.queries, comp_rename_queries_gdh f c, comp_rename_queries_gdh _ k]
  | _, _, _, f, .ite _ c d => by
    simp [Comp.rename, Comp.queries, comp_rename_queries_gdh f c, comp_rename_queries_gdh f d]
  | _, _, _, f, .caseOpt _ n s => by
    simp [Comp.rename, Comp.queries, comp_rename_queries_gdh f n, comp_rename_queries_gdh _ s]
  | _, _, _, f, .caseSum _ l r => by
    simp [Comp.rename, Comp.queries, comp_rename_queries_gdh _ l, comp_rename_queries_gdh _ r]
  | _, _, _, f, .iter _ _ body => by
    simp [Comp.rename, Comp.queries, comp_rename_queries_gdh _ body]
  | _, _, _, f, .findM _ _ p | _, _, _, f, .anyM _ _ p | _, _, _, f, .mapM _ _ p
  | _, _, _, f, .consumeFirstM _ _ p _ | _, _, _, f, .foldM _ _ _ p => by
    simp [Comp.rename, Comp.queries, comp_rename_queries_gdh _ p]

@[simp] private theorem wrapBase_r64 {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase pa sm c).queries zGdh0W kiR64WS = c.queries zPrim0W kiR64WS := by
  simp [wrapBase, bindV, Comp.queries]

@[simp] private theorem wrapSim_r64 {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ]
    (pa : Var Γ₁ paramsTy)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Δ
      (.prod keyIndRespTy simTy)) :
    (wrapSim pa c).queries zGdh0W kiR64WS = c.queries zGdh0W kiR64WS := by
  simp [wrapSim, bindV, Comp.queries]

@[simp] private theorem roRawFallbackC_r64 (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (SignalPqxdh.LegacyCosted.B 192)) :
    (roRawFallbackC (Δ := Δ) K sm sec).queries zGdh0W kiR64WS = 0 := by
  simp [roRawFallbackC, bindV, caseOptV, Comp.queries]

@[simp] private theorem roParsedC_r64 (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (sm : Var Γ₁ simTy) (sec : Var Γ₂ (SignalPqxdh.LegacyCosted.B 192)) :
    (roParsedC (Δ := Δ) K sm sec).queries zGdh0W kiR64WS = 0 := by
  simp [roParsedC, letV, bindV, Comp.queries]

@[simp] private theorem initPrinGdhB_r64 (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) :
    (initPrinGdhB (Δ := Δ) K pa sm bSt u).queries zGdh0W kiR64WS = 0 := by
  simp [initPrinGdhB, letV, bindV, Comp.queries]

@[simp] private theorem genSpkGdhB_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    (genSpkGdhB (Δ := Δ) S K pa sm bSt x).queries zGdh0W kiR64WS = 3 := by
  simp [genSpkGdhB, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem genOpkGdhB_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) :
    (genOpkGdhB (Δ := Δ) S K pa sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [genOpkGdhB, letV, bindV, Comp.queries]

@[simp] private theorem initiateGdhB_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    (initiateGdhB (Δ := Δ) S K pa sm bSt hasOpk x).queries zGdh0W kiR64WS = 0 := by
  simp [initiateGdhB, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem finishAcceptGdhC_r64 (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Γ₇ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] [Ext Γ₇ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ accQTy)
    (ke : Var Γ₅ (.prod .nat principalEntryTy))
    (be : Var Γ₆ (.prod (.prod .nat .nat) spkBundleEntryTy))
    (opkPkOpt : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.opt (SignalPqxdh.LegacyCosted.B 32)))
    (opks' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod (.prod .nat (.prod .nat .nat)) opkEntryTy)))
    (usedO' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (usedN' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.list (.prod .nat (.prod .nat .nat))))
    (kyb' : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ
      (.list (.prod .nat (.prod SignalPqxdh.LegacyCosted.U32
        (.prod SignalPqxdh.LegacyCosted.U32 (SignalPqxdh.LegacyCosted.B 32))))))
    (patchR : Var Γ₇ (.prod drKeyTy (.list fgPatchEntryTy))) :
    (finishAcceptGdhC (Δ := Δ) S K sm bSt hasOpk x ke be opkPkOpt opks' usedO' usedN' kyb' patchR).queries
      zGdh0W kiR64WS = 0 := by
  simp [finishAcceptGdhC, letV, bindV, Comp.queries]

@[simp] private theorem acceptOpkGdhB_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ paramsTy) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    (acceptOpkGdhB (Δ := Δ) S K pa sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [acceptOpkGdhB, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem acceptNoOpkGdhB_r64 (S : Setup) (K : Nat)
    {Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    (acceptNoOpkGdhB (Δ := Δ) S K sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [acceptNoOpkGdhB, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem registerGdhB_r64
    {Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (sk : Var Γ₄ (SignalPqxdh.LegacyCosted.B 32)) :
    (registerGdhB (Δ := Δ) sm bSt sk).queries zGdh0W kiR64WS = 0 := by
  simp [registerGdhB, bindV, Comp.queries]

private theorem gdhHandle_r64_le (S : Setup) (K : Nat) :
    (gdhHandle S K).queries zGdh0W kiR64WS ≤ 3 := by
  simp [gdhHandle, corruptB, testB, revealB, revealSpkB,
    letV, caseOptV, caseSumV, Comp.queries]

@[simp] private theorem koskBundleOkC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (koskBundleOkC (Δ := Δ) S K st bu).queries zPrim0W kiR64WS = 0 := by
  simp [koskBundleOkC, bindV, caseOptV, Comp.queries]

@[simp] private theorem koskSenderOkC_r64 (S : Setup) (K : Nat)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (ik : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 32)) :
    (koskSenderOkC S K st ik).queries zPrim0W kiR64WS = 0 := by
  simp [koskSenderOkC, letV, bindV, Comp.queries]

@[simp] private theorem recordRespC_r64 (S : Setup) (K : Nat)
    {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (p : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (.prod keyIndRespEntryTy keyIndStateTy)) :
    (recordRespC S K p).queries zPrim0W kiR64WS = 0 := by
  simp [recordRespC, letV, bindV, caseOptV, findMV, Comp.queries]

@[simp] private theorem hkdfOrRoC_r64 (K : Nat) (useRo : Bool)
    {Γ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ keyIndStateTy) [Ext Γ Δ]
    (sec : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ (SignalPqxdh.LegacyCosted.B 192)) :
    (hkdfOrRoC K useRo st sec).queries zPrim0W kiR64WS = 0 := by
  cases useRo <;> simp [hkdfOrRoC, letV, caseOptV, bindV, Comp.queries]

@[simp] private theorem acceptKeysC_r64 {Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (inp : Expr SignalPqxdh.LegacyCosted.pqxdhOps Δ accInpTy) :
    (acceptKeysC inp).queries zPrim0W kiR64WS = 0 := rfl

@[simp] private theorem initFinishC_r64 (useRo : Bool) (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Γ₆ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ SignalPqxdh.LegacyCosted.sidT)
    (bu : Var Γ₃ SignalPqxdh.LegacyCosted.bundleT) (uE : Var Γ₄ (.prod .nat principalEntryTy))
    (ekSk : Var Γ₅ (SignalPqxdh.LegacyCosted.B 32))
    (sc : Var Γ₆ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] [Ext Γ₆ Δ] :
    (initFinishC (Δ := Δ) useRo S K st sid bu uE ekSk sc).queries zPrim0W kiR64WS = 0 := by
  cases useRo <;> simp [initFinishC, bindV, letV, caseOptV, findMV, Comp.queries]

@[simp] private theorem preCheckC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (sid : Var Γ₂ SignalPqxdh.LegacyCosted.sidT)
    (u : Var Γ₃ .nat) (bu : Var Γ₄ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    (preCheckC (Δ := Δ) S K st sid u bu).queries zPrim0W kiR64WS = 0 := by
  simp [preCheckC, caseOptV, bindV, Comp.queries]

@[simp] private theorem checkSigsC_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (st : Var Γ₁ keyIndStateTy) (bu : Var Γ₂ SignalPqxdh.LegacyCosted.bundleT)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    (checkSigsC (Δ := Δ) S K st bu).queries zPrim0W kiR64WS = 0 := by
  simp [checkSigsC, bindV, Comp.queries]

@[simp] private theorem onBase_r64 {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (s : Var Γ₁ shcrStTy) [Ext Γ₁ Δ]
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface
        (keyIndStateTy :: Δ) RS) :
    (onBase (Δ := Δ) s br).queries zPrim0W kiR64WS =
      (br .zero).queries zPrim0W kiR64WS := by
  simp [onBase, bindV, letV, Comp.queries]

private theorem shcrKeyInd1KeyProg_r64_le (S : Setup) (Q K q : ℕ) :
    (shcrKeyInd1KeyProg S Q K).totalQueries (fun _ => 0) (sampR64W tlPrimKeyInd.hsmp) q ≤
      3 * q := by
  change (shcrKeyInd1KeyProg S Q K).totalQueries zPrim0W kiR64WS q ≤ 3 * q
  have hInit : (shcrKeyInd1KeyProg S Q K).init.queries zPrim0W kiR64WS = 0 := by
    dsimp only [shcrKeyInd1KeyProg, shcrKeyIndProg]
    split <;> simp [bindV, Comp.queries]
  have hCh : (shcrKeyInd1KeyProg S Q K).chDone.queries zPrim0W kiR64WS = 0 := rfl
  have hRes : (shcrKeyInd1KeyProg S Q K).resume.queries zPrim0W kiR64WS = 0 := by
    simp [shcrKeyInd1KeyProg, shcrResumeC, letV, bindV, Comp.queries]
  have hFin : (shcrKeyInd1KeyProg S Q K).finish.queries zPrim0W kiR64WS = 0 := by
    simp [shcrKeyInd1KeyProg, shcrExtractC, bindV, findMV, Comp.queries]
  have hPost : ∀ {Γ₁ Γ₂ Δ} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (s : Var Γ₁ shcrStTy) (qv : Var Γ₂ keyIndQueryTy),
      (shcr1KeyPostC (Δ := Δ) S K s qv).queries zPrim0W kiR64WS ≤ 3 := by
    intros
    simp only [shcr1KeyPostC, shcrPostTailC,
      _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrin1KeyB,
      corruptB, shcrGenSpkB, genSpkB, genOpkB, shcrInitiateC, shcrAcceptB,
      acceptOpkB, acceptNoOpkB, testB, roB, revealDhB, revealB, registerB, revealSpkB,
      onBase_r64, koskSenderOkC_r64, acceptKeysC_r64, hkdfOrRoC_r64,
      findHonestC_r64, recordRespC_r64, preCheckC_r64, checkSigsC_r64, initFinishC_r64,
      sBytes32_r64, sRandom64_r64, qX25519_r64, qX25519Base_r64, qPow8_r64,
      qSigSign_r64, qKemKeyGen_r64, qKemEncaps_r64, qKemDecaps_r64,
      letV, bindV, caseOptV, caseSumV, Comp.queries, Bool.not_true, ↓reduceIte, Bool.false_eq_true]
    omega
  have hPre : ∀ {Γ₁ Γ₂ Δ} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (s : Var Γ₁ shcrStTy) (qv : Var Γ₂ keyIndQueryTy),
      (shcr1KeyPreC (Δ := Δ) S K s qv).queries zPrim0W kiR64WS ≤ 3 := by
    intro Γ₁ Γ₂ Δ _ _ s qv
    have hp := hPost (Γ₁ := Γ₁) (Γ₂ := Γ₂) (Δ := (.opt pauseTy) :: Δ) s qv
    simp only [shcr1KeyPreC, pauseCheckC, tryPauseC, preCheckC_r64, checkSigsC_r64,
      letV, bindV, caseOptV, caseSumV, Comp.queries]
    omega
  have hHP := hPre (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  have hHQ := hPost (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
    (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero
  unfold TwoStageCostedReduction.totalQueries
  dsimp only [shcrKeyInd1KeyProg, SignalPqxdh.LegacyCosted.keyIndCodec] at hInit hCh hRes hFin ⊢
  rw [hInit, hCh, hRes, hFin]
  have hMax : max
      ((shcr1KeyPreC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
        (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries zPrim0W kiR64WS)
      ((shcr1KeyPostC S K (Γ₁ := [shcrStTy, keyIndQueryTy]) (Γ₂ := [keyIndQueryTy])
        (Δ := [shcrStTy, keyIndQueryTy]) .zero .zero).queries zPrim0W kiR64WS) ≤ 3 := by omega
  have hMul := Nat.mul_le_mul_left q hMax
  omega

@[simp] private theorem liftGdhComp_r64 {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    {t : Ty SignalPqxdh.LegacyCosted.pqSig}
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Γ t) :
    (liftGdhComp c).queries zSigDdh0W kiR64WS = c.queries zGdh0W kiR64WS := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.queries]

@[simp] private theorem sigChalQ_dsl_r64 (m : ℕ+) {Γ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    (msg : Expr SignalPqxdh.LegacyCosted.pqxdhOps Γ (SignalPqxdh.LegacyCosted.B m)) :
    (sigChalQ_dsl m msg).queries zSigDdh0W kiR64WS = 0 := rfl

@[simp] private theorem wrapBase2_r64 {Γ₁ Γ₂ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqPrimIface Δ
      (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).queries zGdh0W kiR64WS = c.queries zPrim0W kiR64WS := by
  simp [wrapBase2, bindV, Comp.queries]

@[simp] private theorem wrapSim2_r64 {Γ₁ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp SignalPqxdh.LegacyCosted.pqxdhOps SignalPqxdh.LegacyCosted.pqGapDhIface Δ
      (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).queries zGdh0W kiR64WS = c.queries zGdh0W kiR64WS := by
  simp [wrapSim2, bindV, Comp.queries]

@[simp] private theorem initPrinGdh2B_r64 (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (u : Var Γ₄ .nat) :
    (initPrinGdh2B (Δ := Δ) K pa sm bSt u).queries zGdh0W kiR64WS = 0 := by
  simp [initPrinGdh2B, letV, bindV, Comp.queries]

@[simp] private theorem genSpkGdh2B_r64 (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat .nat)) :
    (genSpkGdh2B (Δ := Δ) K pa sm bSt x).queries zGdh0W kiR64WS = 3 := by
  simp [genSpkGdh2B, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem genOpkGdh2B_r64 (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ (.prod .nat (.prod .nat .nat))) :
    (genOpkGdh2B (Δ := Δ) K pa sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [genOpkGdh2B, letV, bindV, Comp.queries]

@[simp] private theorem initiateGdh2B_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (hasOpk : Bool) (x : Var Γ₄ initQTy) :
    (initiateGdh2B (Δ := Δ) S K pa sm bSt hasOpk x).queries zGdh0W kiR64WS = 0 := by
  simp [initiateGdh2B, letV, bindV, caseOptV, Comp.queries]

@[simp] private theorem acceptOpkGdh2B_r64 (S : Setup) (K : Nat)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty SignalPqxdh.LegacyCosted.pqSig)}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy) (bSt : Var Γ₃ keyIndStateTy)
    (x : Var Γ₄ accQTy) :
    (acceptOpkGdh2B (Δ := Δ) S K pa sm bSt x).queries zGdh0W kiR64WS = 0 := by
  simp [acceptOpkGdh2B, letV, bindV, caseOptV, Comp.queries]

private theorem gdhHandle2_r64_le (S : Setup) (K : Nat) :
    (gdhHandle2 S K).queries zGdh0W kiR64WS ≤ 3 := by
  simp [gdhHandle2, corruptB, testB, revealB, revealSpkB,
    letV, caseOptV, caseSumV, Comp.queries]

private theorem gdhFinish2_r64 (S : Setup) (K : Nat) :
    (gdhFinish2 S K).queries zGdh0W kiR64WS = 0 := by
  simp [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, letV, bindV, caseOptV, findMV, mapMV, foldMV, Comp.queries]

private theorem bernoulliRatioGdhC_r64 {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).queries zGdh0W kiR64WS = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [bindV, Comp.queries]

private theorem chooseArm2C_r64 {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT} (A B : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).queries zGdh0W kiR64WS = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).queries zGdh0W kiR64WS = 0) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) A B c1 c2).queries zGdh0W kiR64WS = 0 := by
  unfold chooseArm2C
  split_ifs <;> simp [bindV, Comp.queries, bernoulliRatioGdhC_r64, h1, h2]

private theorem initParams1Key2C_r64 (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))) :
    (initParams1Key2C S (Δ := Δ) uv).queries zGdh0W kiR64WS = 0 := by
  have hp : ∀ {Δ' : List PT}, (samplePrin2C S (Δ := Δ')).queries zGdh0W kiR64WS = 0 := by
    intro Δ'; unfold samplePrin2C; split_ifs <;> simp [bindV, Comp.queries]
  have hs : ∀ {Δ' : List PT}, (sampleSpkPair2C S (Δ := Δ')).queries zGdh0W kiR64WS = 0 := by
    intro Δ'; unfold sampleSpkPair2C; split_ifs <;> simp [bindV, Comp.queries]
  have ho : ∀ {Δ' : List PT}, (sampleOpkTriple2C S (Δ := Δ')).queries zGdh0W kiR64WS = 0 := by
    intro Δ'; unfold sampleOpkTriple2C; split_ifs <;> simp [bindV, Comp.queries]
  have hso : ∀ {Δ' : List PT}, (sampleSendOpkTarget2C S (Δ := Δ')).queries zGdh0W kiR64WS = 0 := by
    intro Δ'; unfold sampleSendOpkTarget2C; split_ifs <;> simp [bindV, Comp.queries]
  have hsno : ∀ {Δ' : List PT}, (sampleSendNoOpkTarget2C S (Δ := Δ')).queries zGdh0W kiR64WS = 0 := by
    intro Δ'; unfold sampleSendNoOpkTarget2C; split_ifs <;> simp [bindV, Comp.queries]
  have hst : ∀ {Δ' : List PT}, (sampleSendTarget2C S (Δ := Δ')).queries zGdh0W kiR64WS = 0 := by
    intro Δ'; unfold sampleSendTarget2C
    split_ifs
    · rfl
    · exact chooseArm2C_r64 (Γ₁ := Δ') _ _ _ _ hso hsno
  unfold initParams1Key2C
  split_ifs
  · rfl
  · refine chooseArm2C_r64 _ _ _ _ ?_ ?_
    · intro Δ' _; refine chooseArm2C_r64 _ _ _ _ ?_ ?_ <;>
        (intro Δ'' _; simp [bindV, Comp.queries, hp, hs, hst])
    · intro Δ' _; refine chooseArm2C_r64 _ _ _ _ ?_ ?_ <;>
        (intro Δ'' _; simp [bindV, Comp.queries, hp, hst, hso, ho])

@[simp] private theorem k1_renameComp_queries_r64 :
    ∀ {Γ Δ : List PT} {t : PT} (ρ : Ren Γ Δ)
      (c : Comp pqxdhOps pqSigAndDdhIface Γ t),
      (renameComp ρ c).queries zSigDdh0W kiR64WS = c.queries zSigDdh0W kiR64WS
  | _, _, _, _, .ret _ | _, _, _, _, .sample _ _ | _, _, _, _, .query _ _ => rfl
  | _, _, _, ρ, .bind c k => by
    simp [renameComp, Comp.queries, k1_renameComp_queries_r64 ρ c, k1_renameComp_queries_r64 _ k]
  | _, _, _, ρ, .ite _ c d => by
    simp [renameComp, Comp.queries, k1_renameComp_queries_r64 ρ c, k1_renameComp_queries_r64 ρ d]
  | _, _, _, ρ, .caseOpt _ n s => by
    simp [renameComp, Comp.queries, k1_renameComp_queries_r64 ρ n, k1_renameComp_queries_r64 _ s]
  | _, _, _, ρ, .caseSum _ l r => by
    simp [renameComp, Comp.queries, k1_renameComp_queries_r64 _ l, k1_renameComp_queries_r64 _ r]
  | _, _, _, ρ, .iter _ _ body => by
    simp [renameComp, Comp.queries, k1_renameComp_queries_r64 _ body]
  | _, _, _, ρ, .findM _ _ p | _, _, _, ρ, .anyM _ _ p | _, _, _, ρ, .mapM _ _ p
  | _, _, _, ρ, .consumeFirstM _ _ p _ | _, _, _, ρ, .foldM _ _ _ p => by
    simp [renameComp, Comp.queries, k1_renameComp_queries_r64 _ p]

private theorem fgKeyInd1KeyGapDh2Prog_r64_le (S : Setup) (K q : ℕ) :
    (fgKeyInd1KeyGapDh2Prog S K).totalQueries (fun _ => 0) (sampR64W tlSigDdhKeyInd.hsmp) q ≤
      3 * q := by
  change (fgKeyInd1KeyGapDh2Prog S K).totalQueries zSigDdh0W kiR64WS q ≤ 3 * q
  have hInit : (fgKeyInd1KeyGapDh2Prog S K).init.queries zSigDdh0W kiR64WS = 0 := by
    simp [fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, initAdv4_1Key2Base,
      initParams1Key2C_r64, letV, bindV, Comp.queries]
  have hFin : (fgKeyInd1KeyGapDh2Prog S K).finish.queries zSigDdh0W kiR64WS = 0 := by
    simp [fgKeyInd1KeyGapDh2Prog, gdh1KeyFinish2, gdhFinish2_r64, letV, Comp.queries]
  have hGdh := gdhHandle2_r64_le S K
  have hCall : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (qv : Var Δ keyIndQueryTy),
      (callGdhHandle2 S K st1 qv).queries zSigDdh0W kiR64WS ≤ 3 := by
    intros
    simp only [callGdhHandle2, k1_renameComp_queries_r64, liftGdhComp_r64, letV, bindV, Comp.queries]
    omega
  have hIp : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (st1 : Var Γ₁ gdh1KeyState2Ty) (u : Var Γ₂ .nat),
      (initPrin1Key2B K (Δ := Δ) st1 u).queries zSigDdh0W kiR64WS ≤ 3 := by
    intros
    simp [initPrin1Key2B, letV, bindV, Comp.queries]
  have hGs : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (qv : Var Δ keyIndQueryTy)
      (x : Var Δ (.prod .nat .nat)),
      (genSpk1Key2B S K st1 qv x).queries zSigDdh0W kiR64WS ≤ 3 := by
    intro Δ st1 qv x
    have hc := hCall st1 qv
    simp only [genSpk1Key2B, liftGdhComp_r64, sigChalQ_dsl_r64, gPrim_r64,
      sBytes32_r64, sRandom64_r64, qX25519Base_r64, qKemKeyGen_r64,
      letV, bindV, caseOptV, Comp.queries]
    omega
  have hH : (fgKeyInd1KeyGapDh2Prog S K).handle.queries zSigDdh0W kiR64WS ≤ 3 := by
    dsimp only [fgKeyInd1KeyGapDh2Prog, SignalPqxdh.LegacyCosted.keyIndCodec, gdh1KeyHandle2]
    simp only [caseSumV, Comp.queries, Nat.max_le]
    exact ⟨hIp _ _, hCall _ _, hGs _ _ _, hCall _ _⟩
  unfold CostedReduction.totalQueries
  rw [hInit, hFin]
  have hMul := Nat.mul_le_mul_left q hH
  omega

theorem sigKeyInd1KeyProg_r64_le (S : Setup) (K q : ℕ) :
    (sigKeyInd1KeyProg S K).totalQueries (fun _ => 0) (sampR64W tlSigDdhKeyInd.hsmp) q ≤
      4 * q := by
  change (sigKeyInd1KeyProg S K).totalQueries zSigDdh0W kiR64WS q ≤ 4 * q
  have hInit : (sigKeyInd1KeyProg S K).init.queries zSigDdh0W kiR64WS = 0 := by
    simp [sigKeyInd1KeyProg, bindV, Comp.queries]
  have hFin : (sigKeyInd1KeyProg S K).finish.queries zSigDdh0W kiR64WS = 0 := rfl
  have hGdh := gdhHandle2_r64_le S K
  have hPre : ∀ {Γ₁ Γ₂ Δ} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (s : Var Γ₁ sig1KeyStTy) (qv : Var Γ₂ keyIndQueryTy),
      (sig1KeyPreDispatchC S K (Δ := Δ) s qv).queries zSigDdh0W kiR64WS ≤ 1 := by
    intros
    simp only [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB,
      sig1KeyInitiateCheckC, extract1KeyC,
      s1Prim_r64, qSigDdhSign_r64, honestPeerC_r64,
      sBytes32_r64, sRandom64_r64, qX25519Base_r64, qKemKeyGen_r64, qSigVerify_r64,
      letV, bindV, caseOptV, caseSumV, Comp.queries]
    omega
  have hDel : ∀ {Γ₁ Γ₂ Δ} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (s : Var Γ₁ sig1KeyStTy) (qv : Var Γ₂ keyIndQueryTy),
      (delegateFgC S K (Δ := Δ) s qv).queries zSigDdh0W kiR64WS ≤ 3 := by
    intros
    simp only [delegateFgC, liftGdhToSigDdh_r64, comp_rename_queries_gdh, letV, bindV, Comp.queries]
    omega
  have hH : (sigKeyInd1KeyProg S K).handle.queries zSigDdh0W kiR64WS ≤ 4 := by
    dsimp only [sigKeyInd1KeyProg, SignalPqxdh.LegacyCosted.keyIndCodec, sig1KeyHandleC]
    have hp := hPre (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
      (Δ := [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
    have hd := hDel (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
      (Δ := .unit :: .sum S1RS .unit :: [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
    simp only [bindV, caseSumV, Comp.queries]
    omega
  unfold CostedReduction.totalQueries
  rw [hInit, hFin]
  have hMul := Nat.mul_le_mul_left q hH
  omega

end Sig1KeyR64

section OneKeySizeBounds

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open _root_.Proofs.SignalPqxdh.Security
open Computational.Proofs.SignalPqxdh.AtomicLift

set_option allowUnsafeReducibility true in
attribute [local implicit_reducible] sigAndDdhOracle gapDhDdhOracle

@[simp] private theorem k1_liftBase_size {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    (liftBase (C := C) c).size = c.size := by
  induction c <;> simp_all [liftBase, Comp.size, pqChalIface, pqPrimIface]

@[simp] private theorem k1_gPrim_size {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (gPrim c).size = c.size := k1_liftBase_size c

@[simp] private theorem k1_s1Prim_size {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    (s1Prim c).size = c.size := k1_liftBase_size c

@[simp] private theorem k1_liftGdhToSigDdh_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhToSigDdh c).size = c.size := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, Comp.size]

@[simp] private theorem k1_liftGdhComp_size {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    (liftGdhComp c).size = c.size := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, Comp.size]

@[simp] private theorem k1_expr_rename_size {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (e : Expr pqxdhOps Γ τ) :
    (e.rename ρ).size = e.size := by
  induction e generalizing Δ <;> simp only [Expr.rename, Expr.size, *]

@[simp] private theorem k1_comp_rename_size {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (c : Comp pqxdhOps I Γ τ) :
    (c.rename ρ).size = c.size := by
  induction c generalizing Δ <;> simp only [Comp.rename, Comp.size, k1_expr_rename_size, *]

@[simp] private theorem k1_renameExpr_size {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (e : Expr pqxdhOps Γ τ) :
    (renameExpr ρ e).size = e.size := by
  induction e generalizing Δ <;> simp only [renameExpr, Expr.size, *]

@[simp] private theorem k1_renameComp_size {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (c : Comp pqxdhOps I Γ τ) :
    (renameComp ρ c).size = c.size := by
  induction c generalizing Δ <;> simp only [renameComp, Comp.size, k1_renameExpr_size, *]

section K1SizeSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {Γ Δ : List PT} {τ τ₁ τ₂ : PT}

@[simp] private theorem k1_v_size [Ext Γ Δ] (x : Var Γ τ) : (v (Δ := Δ) x).size = 1 := rfl
@[simp] private theorem k1_bindV_size (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (bindV m k).size = m.size + (k .zero).size + 1 := rfl
@[simp] private theorem k1_letV_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (letV (I := I) e k).size = e.size + 1 + (k .zero).size + 1 := rfl
@[simp] private theorem k1_caseOptV_size (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    (caseOptV o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] private theorem k1_caseSumV_size (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    (caseSumV s kl kr).size = s.size + (kl .zero).size + (kr .zero).size + 1 := rfl
@[simp] private theorem k1_findMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (findMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem k1_anyMV_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    (anyMV K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem k1_eLet_size (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eLet e k).size = e.size + (k .zero).size + 1 := rfl
@[simp] private theorem k1_eCaseOpt_size (o : Expr pqxdhOps Γ (.opt τ₁)) (kn : Expr pqxdhOps Γ τ₂)
    (ks : Var (τ₁ :: Γ) τ₁ → Expr pqxdhOps (τ₁ :: Γ) τ₂) :
    (eCaseOpt o kn ks).size = o.size + kn.size + (ks .zero).size + 1 := rfl
@[simp] private theorem k1_eFind_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eFind K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem k1_eAny_size (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Expr pqxdhOps (τ :: Γ) .bool) :
    (eAny K xs p).size = xs.size + (p .zero).size + bits K + 1 := rfl
@[simp] private theorem k1_litB_size (w : ℕ+) (bs : Bytes) : (litB w bs (Γ := Γ)).size = 2 := rfl
@[simp] private theorem k1_widenB_size (w d : ℕ+) (e : Expr pqxdhOps Γ (B w)) :
    (widenB w d e).size = e.size + 1 := rfl
@[simp] private theorem k1_eqB_size {m n : ℕ+} (a : Expr pqxdhOps Γ (B m)) (b : Expr pqxdhOps Γ (B n)) :
    (eqB a b).size = a.size + b.size + 2 := rfl
@[simp] private theorem k1_u32OfNat_size (e : Expr pqxdhOps Γ .nat) : (u32OfNat e).size = e.size + 1 := rfl
@[simp] private theorem k1_sBool_size : (sBool (Γ := Γ)).size = 2 := rfl
@[simp] private theorem k1_sBytes32_size : (sBytes32 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem k1_sRandom64_size : (sRandom64 (Γ := Γ)).size = 2 := rfl
@[simp] private theorem k1_sIndex_size (N : ℕ) : (sIndex N (Γ := Γ)).size = 2 := rfl
@[simp] private theorem k1_qX25519Base_size (e : Expr pqxdhOps Γ (B 32)) :
    (qX25519Base e).size = e.size + 1 := rfl
@[simp] private theorem k1_qPow8_size (e : Expr pqxdhOps Γ (B 32)) :
    (qPow8 e).size = e.size + 1 := rfl
@[simp] private theorem k1_qSigPkGen_size (e : Expr pqxdhOps Γ (B 32)) :
    (qSigPkGen e).size = e.size + 1 := rfl
@[simp] private theorem k1_qSigVerify_size (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    (qSigVerify m e).size = e.size + 1 := rfl
@[simp] private theorem k1_qKemKeyGen_size (e : Expr pqxdhOps Γ (B 64)) :
    (qKemKeyGen e).size = e.size + 1 := rfl
@[simp] private theorem k1_qSigDdhSign_size (m : ℕ+) (msg : Expr pqxdhOps Γ (B m)) :
    (qSigDdhSign m msg).size = msg.size + 1 := rfl
@[simp] private theorem k1_sigChalQ_dsl_size (m : ℕ+) (msg : Expr pqxdhOps Γ (B m)) :
    (sigChalQ_dsl m msg).size = msg.size + 1 := rfl
@[simp] private theorem k1_encEC_size (e : Expr pqxdhOps Γ (B 32)) : (encEC e).size = e.size + 1 := rfl
@[simp] private theorem k1_encKEM_size (e : Expr pqxdhOps Γ (B 1568)) : (encKEM e).size = e.size + 1 := rfl

end K1SizeSimp

private theorem k1_bits_mono_local {x y : ℕ} (h : x ≤ y) : bits x ≤ bits y := by
  unfold bits
  exact Nat.add_le_add_right (Nat.log_mono_right h) 1

private theorem k1_bits_le_of_le_four_mul_sq {x N : ℕ} (h : x ≤ 4 * (N * N)) :
    bits x ≤ 2 * bits N + 3 := by
  have h1 := k1_bits_mono_local h
  have h2 := bits_mul 4 (N * N)
  have h3 := bits_mul N N
  have h4 : bits 4 = 3 := by decide
  omega

private def k1_qSampWeight {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T} :
    {Γ : List PT} → {t : PT} → Comp pqxdhOps I Γ t → ℕ
  | _, _, .ret _ => 0
  | _, _, .bind c k => k1_qSampWeight c + k1_qSampWeight k
  | _, _, .ite _ c d => k1_qSampWeight c + k1_qSampWeight d
  | _, _, .caseOpt _ c d => k1_qSampWeight c + k1_qSampWeight d
  | _, _, .caseSum _ c d => k1_qSampWeight c + k1_qSampWeight d
  | _, _, .sample _ _ => 17
  | _, _, .query _ _ => 8
  | _, _, .iter _ _ body => k1_qSampWeight body
  | _, _, .findM _ _ p => k1_qSampWeight p
  | _, _, .anyM _ _ p => k1_qSampWeight p
  | _, _, .mapM _ _ p => k1_qSampWeight p
  | _, _, .consumeFirstM _ _ p _ => k1_qSampWeight p
  | _, _, .foldM _ _ _ f => k1_qSampWeight f

private theorem k1_mapComp_size_le_add_qSampWeight {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) :
    ∀ {Γ : List PT} {t : PT} (c : Comp pqxdhOps I Γ t),
      (mapComp tl c).size ≤ c.size + k1_qSampWeight c + compLitSize c
  | _, _, .ret e => by
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .bind c k => by
    have ihc := k1_mapComp_size_le_add_qSampWeight tl htl c
    have ihk := k1_mapComp_size_le_add_qSampWeight tl htl k
    simp only [mapComp, Comp.size, k1_qSampWeight, compLitSize]; omega
  | _, _, .ite b c d => by
    have ihc := k1_mapComp_size_le_add_qSampWeight tl htl c
    have ihd := k1_mapComp_size_le_add_qSampWeight tl htl d
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .caseOpt b c d => by
    have ihc := k1_mapComp_size_le_add_qSampWeight tl htl c
    have ihd := k1_mapComp_size_le_add_qSampWeight tl htl d
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .caseSum b c d => by
    have ihc := k1_mapComp_size_le_add_qSampWeight tl htl c
    have ihd := k1_mapComp_size_le_add_qSampWeight tl htl d
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | Γ', _, .sample s e => by
    have he := one_le_expr_size e
    have hs := mapSampH_size_le A tl.hsmp (Γ := embedCtx Γ') s
    simp only [mapComp, mapSampCast, Comp.size, k1_qSampWeight, compLitSize]; omega
  | _, _, .query g e => by
    have hq := htl g (mapExpr e)
    rw [mapExpr_size] at hq
    simp only [mapComp, Comp.size, k1_qSampWeight, compLitSize]; omega
  | _, _, .iter n e body => by
    have ih := k1_mapComp_size_le_add_qSampWeight tl htl body
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .findM K l p => by
    have ih := k1_mapComp_size_le_add_qSampWeight tl htl p
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .anyM K l p => by
    have ih := k1_mapComp_size_le_add_qSampWeight tl htl p
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .mapM K l p => by
    have ih := k1_mapComp_size_le_add_qSampWeight tl htl p
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .consumeFirstM K l p mk => by
    have ih := k1_mapComp_size_le_add_qSampWeight tl htl p
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega
  | _, _, .foldM K l z f => by
    have ih := k1_mapComp_size_le_add_qSampWeight tl htl f
    simp only [mapComp, Comp.size, mapExpr_size, k1_qSampWeight, compLitSize]; omega

private theorem k1_liftKeyInd1Stage_size_le_add_qSampWeight {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (htl : tl.QuerySizeLe) (S : Setup)
    {rIn out : PT}
    (R : CostedReduction pqxdhOps I (keyIndSpec S) (keyIndCodec S) rIn .unit .bool out) :
    (liftKeyInd1Stage tl S R).size ≤
      R.size + (k1_qSampWeight R.init + k1_qSampWeight R.handle + k1_qSampWeight R.finish) +
        red1LitSize R + 402 := by
  have hI : (liftKeyInd1Stage tl S R).init.size ≤
      R.init.size + k1_qSampWeight R.init + compLitSize R.init :=
    k1_mapComp_size_le_add_qSampWeight tl htl R.init
  have hH : (liftKeyInd1Stage tl S R).handle.size ≤
      R.handle.size + k1_qSampWeight R.handle + compLitSize R.handle + 402 := by
    have hq := finKeyIndQToNatExpr_v1_size_le S (σ' := embedTy R.σ)
    have hm := k1_mapComp_size_le_add_qSampWeight tl htl R.handle
    have hcr := compRename_size (fun {a} => swapHandlerVar (Q_fin := (pqKeyIndCodec S).Q)) (mapComp tl R.handle)
    change ((finKeyIndQToNatExpr S .v1).size + 1) +
      (compRename (fun {a} => swapHandlerVar (Q_fin := (pqKeyIndCodec S).Q)) (mapComp tl R.handle)).size + 1 ≤ _
    omega
  have hF : (liftKeyInd1Stage tl S R).finish.size ≤
      R.finish.size + k1_qSampWeight R.finish + compLitSize R.finish :=
    k1_mapComp_size_le_add_qSampWeight tl htl R.finish
  unfold CostedReduction.size red1LitSize
  omega

section K1QSampWeightSimp

variable {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
  {Γ : List PT} {τ τ₁ τ₂ : PT}

@[simp] private theorem k1_liftBase_qsw {C : ChallengerOracle} (c : Comp pqxdhOps pqPrimIface Γ τ) :
    k1_qSampWeight (liftBase (C := C) c) = k1_qSampWeight c := by
  induction c <;> simp_all [liftBase, k1_qSampWeight, pqChalIface, pqPrimIface]
@[simp] private theorem k1_gPrim_qsw (c : Comp pqxdhOps pqPrimIface Γ τ) :
    k1_qSampWeight (gPrim c) = k1_qSampWeight c := k1_liftBase_qsw c
@[simp] private theorem k1_liftGdhComp_qsw (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    k1_qSampWeight (liftGdhComp c) = k1_qSampWeight c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, k1_qSampWeight]
@[simp] private theorem k1_renameComp_qsw {Δ : List PT} (ρ : Ren Γ Δ) (c : Comp pqxdhOps I Γ τ) :
    k1_qSampWeight (renameComp ρ c) = k1_qSampWeight c := by
  induction c generalizing Δ <;> simp only [renameComp, k1_qSampWeight, *]
@[simp] private theorem k1_bindV_qsw (m : Comp pqxdhOps I Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    k1_qSampWeight (bindV m k) = k1_qSampWeight m + k1_qSampWeight (k .zero) := rfl
@[simp] private theorem k1_letV_qsw (e : Expr pqxdhOps Γ τ₁)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    k1_qSampWeight (letV (I := I) e k) = k1_qSampWeight (k .zero) :=
  Nat.zero_add _
@[simp] private theorem k1_caseOptV_qsw (o : Expr pqxdhOps Γ (.opt τ₁))
    (kn : Comp pqxdhOps I Γ τ₂) (ks : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    k1_qSampWeight (caseOptV o kn ks) = k1_qSampWeight kn + k1_qSampWeight (ks .zero) := rfl
@[simp] private theorem k1_caseSumV_qsw (s : Expr pqxdhOps Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₂ :: Γ) τ) :
    k1_qSampWeight (caseSumV s kl kr) = k1_qSampWeight (kl .zero) + k1_qSampWeight (kr .zero) := rfl
@[simp] private theorem k1_findMV_qsw (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    k1_qSampWeight (findMV K xs p) = k1_qSampWeight (p .zero) := rfl
@[simp] private theorem k1_anyMV_qsw (K : Nat) (xs : Expr pqxdhOps Γ (.list τ))
    (p : Var (τ :: Γ) τ → Comp pqxdhOps I (τ :: Γ) .bool) :
    k1_qSampWeight (anyMV K xs p) = k1_qSampWeight (p .zero) := rfl
@[simp] private theorem k1_mapMV_qsw (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) :
    k1_qSampWeight (mapMV K xs f) = k1_qSampWeight (f .zero) := rfl
@[simp] private theorem k1_foldMV_qsw (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (init : Expr pqxdhOps Γ τ₂)
    (f : Var (τ₁ :: τ₂ :: Γ) τ₁ → Var (τ₁ :: τ₂ :: Γ) τ₂ → Comp pqxdhOps I (τ₁ :: τ₂ :: Γ) τ₂) :
    k1_qSampWeight (foldMV K xs init f) = k1_qSampWeight (f .zero (.succ .zero)) := rfl
@[simp] private theorem k1_sBool_qsw : k1_qSampWeight (sBool (Γ := Γ)) = 17 := rfl
@[simp] private theorem k1_sBytes32_qsw : k1_qSampWeight (sBytes32 (Γ := Γ)) = 17 := rfl
@[simp] private theorem k1_sRandom64_qsw : k1_qSampWeight (sRandom64 (Γ := Γ)) = 17 := rfl
@[simp] private theorem k1_sDrKey96_qsw : k1_qSampWeight (sDrKey96 (Γ := Γ)) = 17 := rfl
@[simp] private theorem k1_sIndex_qsw (N : ℕ) : k1_qSampWeight (sIndex N (Γ := Γ)) = 17 := rfl
@[simp] private theorem k1_qX25519_qsw (e : Expr pqxdhOps Γ (.prod (B 32) (B 32))) :
    k1_qSampWeight (qX25519 e) = 8 := rfl
@[simp] private theorem k1_qX25519Base_qsw (e : Expr pqxdhOps Γ (B 32)) :
    k1_qSampWeight (qX25519Base e) = 8 := rfl
@[simp] private theorem k1_qIsCanonical_qsw (e : Expr pqxdhOps Γ (B 32)) :
    k1_qSampWeight (qIsCanonical e) = 8 := rfl
@[simp] private theorem k1_qPow8_qsw (e : Expr pqxdhOps Γ (B 32)) : k1_qSampWeight (qPow8 e) = 8 := rfl
@[simp] private theorem k1_qSigPkGen_qsw (e : Expr pqxdhOps Γ (B 32)) :
    k1_qSampWeight (qSigPkGen e) = 8 := rfl
@[simp] private theorem k1_qSigSign_qsw (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    k1_qSampWeight (qSigSign m e) = 8 := rfl
@[simp] private theorem k1_qSigVerify_qsw (m : ℕ+) (e : Expr pqxdhOps Γ (.prod (B 32) (.prod (B m) (B 64)))) :
    k1_qSampWeight (qSigVerify m e) = 8 := rfl
@[simp] private theorem k1_qKemKeyGen_qsw (e : Expr pqxdhOps Γ (B 64)) :
    k1_qSampWeight (qKemKeyGen e) = 8 := rfl
@[simp] private theorem k1_qKemEncaps_qsw (e : Expr pqxdhOps Γ (.prod (B 1568) (B 32))) :
    k1_qSampWeight (qKemEncaps e) = 8 := rfl
@[simp] private theorem k1_qKemDecaps_qsw (e : Expr pqxdhOps Γ (.prod (B 3168) (B 1568))) :
    k1_qSampWeight (qKemDecaps e) = 8 := rfl
@[simp] private theorem k1_qHkdfDerive96_qsw (w : ℕ+) (e : Expr pqxdhOps Γ (B w)) :
    k1_qSampWeight (qHkdfDerive96 w e) = 8 := rfl
@[simp] private theorem k1_ddhQ_qsw (x y z : Expr pqxdhOps Γ (B 32)) :
    k1_qSampWeight (ddhQ x y z) = 8 := rfl
@[simp] private theorem k1_sigChalQ_dsl_qsw (m : ℕ+) (msg : Expr pqxdhOps Γ (B m)) :
    k1_qSampWeight (sigChalQ_dsl m msg) = 8 := rfl

end K1QSampWeightSimp

set_option linter.unusedSimpArgs false in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
private theorem k1_gdhHandle_qSampWeight_le (S : Setup) (K : Nat) :
    k1_qSampWeight (gdhHandle S K) ≤ 10000 := by
  simp (config := { maxSteps := 1000000 }) only [gdhHandle, initPrinGdhB, corruptB, genSpkGdhB,
    genOpkGdhB, initiateGdhB, finishAcceptGdhC, acceptOpkGdhB, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase, wrapSim,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC,
    ddhEqC, ddhEqOptC, entryMatchesC, fgPatchC,
    findHonestC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, partnerC,
    chooseRespRandC, chooseInitRandC,
    k1_gPrim_qsw, k1_letV_qsw, k1_bindV_qsw, k1_caseOptV_qsw, k1_caseSumV_qsw,
    k1_findMV_qsw, k1_anyMV_qsw, k1_mapMV_qsw, k1_foldMV_qsw,
    k1_sBool_qsw, k1_sBytes32_qsw, k1_sRandom64_qsw, k1_sDrKey96_qsw, k1_sIndex_qsw,
    k1_qX25519_qsw, k1_qX25519Base_qsw, k1_qIsCanonical_qsw, k1_qPow8_qsw,
    k1_qSigPkGen_qsw, k1_qSigSign_qsw, k1_qSigVerify_qsw,
    k1_qKemKeyGen_qsw, k1_qKemEncaps_qsw, k1_qKemDecaps_qsw, k1_ddhQ_qsw,
    k1_qSampWeight, ↓reduceIte, Bool.false_eq_true]
  omega

set_option linter.unusedSimpArgs false in
private theorem k1_gdhFinish_qSampWeight_le (S : Setup) (K : Nat) :
    k1_qSampWeight (gdhFinish S K) ≤ 500 := by
  simp only [gdhFinish, extractMode0C, logFindC, spkPowsC, findMapStepC,
    initDh1CandC, respDh1CandC,
    k1_gPrim_qsw, k1_letV_qsw, k1_bindV_qsw, k1_caseOptV_qsw,
    k1_findMV_qsw, k1_mapMV_qsw, k1_foldMV_qsw,
    k1_qPow8_qsw, k1_qX25519_qsw, k1_ddhQ_qsw, k1_qSampWeight]
  omega

@[simp] private theorem k1_s1Prim_qsw {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqPrimIface Γ τ) :
    k1_qSampWeight (s1Prim c) = k1_qSampWeight c := k1_liftBase_qsw c

@[simp] private theorem k1_liftGdhToSigDdh_qsw {Γ : List PT} {τ : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ τ) :
    k1_qSampWeight (liftGdhToSigDdh c) = k1_qSampWeight c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, k1_qSampWeight]

@[simp] private theorem k1_qSigDdhSign_qsw (m : ℕ+) {Γ : List PT}
    (msg : Expr pqxdhOps Γ (B m)) :
    k1_qSampWeight (qSigDdhSign m msg) = 8 := rfl

@[simp] private theorem k1_liftBase_litSize {C : ChallengerOracle} {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (liftBase (C := C) c) = compLitSize c := by
  induction c <;> simp_all [liftBase, compLitSize, pqChalIface, pqPrimIface]

@[simp] private theorem k1_gPrim_litSize {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (gPrim c) = compLitSize c := k1_liftBase_litSize c

@[simp] private theorem k1_s1Prim_litSize {Γ : List PT} {t : PT} (c : Comp pqxdhOps pqPrimIface Γ t) :
    compLitSize (s1Prim c) = compLitSize c := k1_liftBase_litSize c

@[simp] private theorem k1_liftGdhToSigDdh_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhToSigDdh c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhToSigDdh, compLitSize]

@[simp] private theorem k1_liftGdhComp_litSize {Γ : List PT} {t : PT}
    (c : Comp pqxdhOps pqGapDhIface Γ t) :
    compLitSize (liftGdhComp c) = compLitSize c := by
  induction c with
  | query g _ => rcases g with _ | ⟨⟩ <;> rfl
  | sample _ _ => rfl
  | _ => simp_all [liftGdhComp, compLitSize]

@[simp] private theorem k1_expr_rename_litSize {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (e : Expr pqxdhOps Γ τ) :
    exprLitSize (e.rename ρ) = exprLitSize e := by
  induction e generalizing Δ <;> simp only [Expr.rename, exprLitSize, *]

@[simp] private theorem k1_comp_rename_litSize {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : ∀ {t}, Var Γ t → Var Δ t) (c : Comp pqxdhOps I Γ τ) :
    compLitSize (c.rename ρ) = compLitSize c := by
  induction c generalizing Δ <;> simp only [Comp.rename, compLitSize, k1_expr_rename_litSize, *]

@[simp] private theorem k1_renameExpr_litSize {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (e : Expr pqxdhOps Γ τ) :
    exprLitSize (renameExpr ρ e) = exprLitSize e := by
  induction e generalizing Δ <;> simp only [renameExpr, exprLitSize, *]

@[simp] private theorem k1_renameComp_litSize {ι : Type} {T : OracleSpec ι} {I : Iface pqSig T}
    {Γ Δ : List PT} {τ : PT}
    (ρ : Ren Γ Δ) (c : Comp pqxdhOps I Γ τ) :
    compLitSize (renameComp ρ c) = compLitSize c := by
  induction c generalizing Δ <;> simp only [renameComp, compLitSize, k1_renameExpr_litSize, *]

set_option linter.unusedSimpArgs false in
private theorem k1_initPrin1KeyB_litSize_eq (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (st : Var Γ₁ keyIndStateTy) (u : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrin1KeyB (Δ := Δ) K st u) =
      compLitSize (_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinB (Δ := Δ) K st u) := by
  simp only [_root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrin1KeyB,
    _root_.SignalPqxdh.Security.ReductionDsl.KeyInd.initPrinB, bindV, eAny, natEq,
    stPrin, stSecb, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv,
    stUpd, stMk, peMk, rs, rNone, rInitPrin,
    sBytes32, qX25519Base, qSigPkGen, v, compLitSize, exprLitSize, pqOpLitSize]

private theorem k1_shcr1KeyPostC_litSize_eq (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (shcr1KeyPostC (Δ := Δ) S K s q) = compLitSize (shcrPostC (Δ := Δ) S K s q) := by
  rw [shcrPostC_eq_tail]
  simp only [shcr1KeyPostC, caseSumV, onBase, bindV, letV, k1_initPrin1KeyB_litSize_eq, compLitSize]

private theorem k1_shcr1KeyPreC_litSize_eq (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    (s : Var Γ₁ shcrStTy) (q : Var Γ₂ keyIndQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    compLitSize (shcr1KeyPreC (Δ := Δ) S K s q) = compLitSize (shcrPreC (Δ := Δ) S K s q) := by
  simp only [shcr1KeyPreC, shcrPreC, bindV, caseOptV, k1_shcr1KeyPostC_litSize_eq, compLitSize]

private theorem k1_shcrKeyInd1KeyProg_litSize_eq (S : Setup) (Q K : Nat) :
    red2LitSize (shcrKeyInd1KeyProg S Q K) = red2LitSize (shcrKeyIndProg S Q K) := by
  dsimp only [red2LitSize, shcrKeyInd1KeyProg, shcrKeyIndProg, SignalPqxdh.LegacyCosted.keyIndCodec]
  rw [k1_shcr1KeyPreC_litSize_eq, k1_shcr1KeyPostC_litSize_eq]

set_option linter.unusedSimpArgs false in
private theorem k1_sig1KeyPreDispatchC_litSize_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    compLitSize (sig1KeyPreDispatchC S K (Δ := Δ) s q) ≤ 200 := by
  simp only [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB,
    sig1KeyInitiateCheckC, extract1KeyC, honestPeerC, findHonestC,
    s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd,
    peIkAPk, peMk, sbSpkPk, sbPqspkPk, sbMk,
    buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig, buMk,
    rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq,
    encEC, encKEM, widenEC, consB, widenB,
    letV, bindV, caseOptV, caseSumV, findMV,
    k1_s1Prim_litSize, s1Prim, liftBase,
    qSigDdhSign, qSigVerify, qPow8, sBytes32, sRandom64, qX25519Base, qKemKeyGen,
    eCaseOpt, eAny, eFind, eqB, litB, u32OfNat,
    v, compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
  omega

@[simp] private theorem k1_F_X25519_length : F_X25519.length = 32 := by decide

@[simp] private theorem k1_callGdhHandle2_litSize (S : Setup) (K : Nat) {Δ : List PT}
    (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy) :
    compLitSize (callGdhHandle2 S K st1 q) = compLitSize (gdhHandle2 S K) := by
  simp only [callGdhHandle2, letV, bindV, v, compLitSize, exprLitSize,
    k1_renameComp_litSize, k1_liftGdhComp_litSize, Nat.add_zero, Nat.zero_add]

set_option linter.unusedSimpArgs false in
private theorem k1_gdhFinish2_litSize_le (S : Setup) (K : Nat) :
    compLitSize (gdhFinish2 S K) ≤ 1000 := by
  simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC, findMapStep2C,
    initDh1CandC, respDh1CandC, lookupFromPowsE, respBundleKeyE, slice32,
    smBase, smLog, smPows, pa2U, pa2V, pa2Mode, natEq, nat2Eq,
    letV, bindV, caseOptV, findMV, mapMV, foldMV,
    eCaseOpt, eCaseSum, eFind, eMap,
    k1_gPrim_litSize, gPrim, liftBase, qPow8, qX25519, ddhQ,
    litB, takeKB, dropB, eqB, v,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, k1_F_X25519_length,
    Nat.add_zero, Nat.zero_add]
  omega

set_option linter.unusedSimpArgs false in
private theorem k1_gdhHandle2_litSize_le (S : Setup) (K : Nat) :
    compLitSize (gdhHandle2 S K) ≤ 10000 := by
  simp (config := { maxSteps := 1000000 }) only [gdhHandle2, initPrinGdh2B, corruptB, genSpkGdh2B,
    genOpkGdh2B, initiateGdh2B, finishAcceptGdhC, acceptOpkGdh2B, acceptNoOpkGdhB,
    testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
    wrapBase2, wrapSim2, ephSidMatchesE,
    fePos1, fePos2, fePos3, fePos4, feSs, feDk, feMk,
    pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag, pa2EphTarget,
    pa2SpkTarget, pa2OpkMode, pa2OpkTarget, pa2Mode,
    smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
    stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
    peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk, peUpd,
    sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk, sbUpd,
    oeMk, oeUpd,
    buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
    hdIkAPk, hdEkAPk, hdSpkId, hdOpkId, hdPqspkId, hdKemCt, hdMk,
    seSid, seHdr, sePeerSpk, seTested, seRevealed, seMk, seUpd,
    reSid, reHdr, reMk, reUpd,
    qKJO, qK, qJ, qO, qHdr, rs, slice32,
    rNone, rInitPrin, rPk, rCorr, rBundle, rHdr, rInitUnfresh, rAccFresh, rDrKey, rSpkSk,
    initSidE,
    natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
    optU32Eq, optBytesEq, getDBytes, isSomeE, optFst, optSnd, nonZero32,
    orE, mulRight, eLet2, isAdvPowsE,
    mkSecretPosC, mkPairPosC, computePosC, computeOptPosInitC,
    ddhEqC, ddhEqOptC, entryMatchesC, fgPatchC,
    findHonestC, isAdvRegC, isGameSpkC, isGameOpkC, koskSenderOkPowsC, koskBundleOkPowsC,
    lookupSpkSkC, resolveSigPkC, honestPeerC, checkProvC, partnerC,
    chooseRespRandC, chooseInitRandC,
    k1_gPrim_litSize, gPrim, liftBase,
    v, letV, bindV, caseOptV, caseSumV, findMV, anyMV, mapMV, foldMV,
    eLet, eCaseOpt, eCaseSum, eFind, eAny, eMap,
    litB, catB, consB, widenB, takeKB, dropB, lenB, eqB, u32OfNat, eqU32,
    sBool, sBytes32, sRandom64, sDrKey96, sIndex,
    qX25519, qX25519Base, qIsCanonical, qPow8,
    qSigPkGen, qSigSign, qSigVerify,
    qKemKeyGen, qKemEncaps, qKemDecaps, qHkdfDerive96, ddhQ, encEC, encKEM,
    compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, List.length_cons, List.length_replicate, k1_F_X25519_length,
    Nat.add_zero, Nat.zero_add,
    ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, Bool.not_true, Bool.not_false]
  omega

set_option linter.unusedSimpArgs false in
private theorem k1_delegateFgC_litSize_le (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] (s : Var Γ₁ sig1KeyStTy) (q : Var Γ₂ keyIndQueryTy) :
    compLitSize (delegateFgC S K (Δ := Δ) s q) ≤ 10200 := by
  have hH := k1_gdhHandle2_litSize_le S K
  simp only [delegateFgC, pa2Zero, pa2Mk, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery,
    s1Mk, s1Upd, letV, bindV, k1_liftGdhToSigDdh_litSize, k1_comp_rename_litSize,
    litB, v, compLitSize, exprLitSize, pqOpLitSize,
    List.length_nil, Nat.add_zero, Nat.zero_add]
  generalize compLitSize (gdhHandle2 S K) = cGH at hH ⊢
  omega

private theorem k1_sig1KeyHandleC_litSize_le (S : Setup) (K : Nat) :
    compLitSize (sig1KeyHandleC S K) ≤ 10500 := by
  have hPre := k1_sig1KeyPreDispatchC_litSize_le S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  have hDel := k1_delegateFgC_litSize_le S K
    (Γ₁ := [sig1KeyStTy, keyIndQueryTy]) (Γ₂ := [sig1KeyStTy, keyIndQueryTy])
    (Δ := .unit :: (.sum S1RS .unit) :: [sig1KeyStTy, keyIndQueryTy]) .zero (.succ .zero)
  simp only [sig1KeyHandleC, bindV, caseSumV, v, compLitSize, exprLitSize]
  omega

set_option linter.unusedSimpArgs false in
private theorem k1_sigKeyInd1KeyProg_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (sigKeyInd1KeyProg S K) ≤ 20000 := by
  have hH := k1_sig1KeyHandleC_litSize_le S K
  have hI : compLitSize (sigKeyInd1KeyProg S K).init ≤ 100 := by
    dsimp only [sigKeyInd1KeyProg]
    simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
      bindV, k1_s1Prim_litSize, s1Prim, liftBase, sIndex, sBool, v,
      compLitSize, exprLitSize, pqOpLitSize, Nat.add_zero, Nat.zero_add]
    omega
  have hF : compLitSize (sigKeyInd1KeyProg S K).finish ≤ 100 := by
    dsimp only [sigKeyInd1KeyProg]
    simp only [s1Forgery, eCaseOpt, litB, v, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, Nat.add_zero, Nat.zero_add]
    omega
  have hEq : red1LitSize (sigKeyInd1KeyProg S K) =
      compLitSize (sigKeyInd1KeyProg S K).init + compLitSize (sig1KeyHandleC S K) +
      compLitSize (sigKeyInd1KeyProg S K).finish := rfl
  rw [hEq]
  generalize compLitSize (sigKeyInd1KeyProg S K).init = cI at hI ⊢
  generalize compLitSize (sig1KeyHandleC S K) = cH at hH ⊢
  generalize compLitSize (sigKeyInd1KeyProg S K).finish = cF at hF ⊢
  omega

private theorem k1_bernoulliRatioGdhC_litSize {Δ : List PT} (A B : Nat) :
    compLitSize (bernoulliRatioGdhC (Δ := Δ) A B) = 0 := by
  unfold bernoulliRatioGdhC
  split_ifs <;> simp [bindV, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize]

private theorem k1_chooseArm2C_litSize {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {α : PT} (w1 w2 : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' α)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], compLitSize (c1 (Δ' := Δ')) = 0)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], compLitSize (c2 (Δ' := Δ')) = 0) :
    compLitSize (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) w1 w2 c1 c2) = 0 := by
  unfold chooseArm2C
  split_ifs <;> simp [bindV, v, compLitSize, exprLitSize, k1_bernoulliRatioGdhC_litSize, h1, h2]

private theorem k1_initParams1Key2C_litSize (S : Setup) {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (uv : Var Γ₁ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))) :
    compLitSize (initParams1Key2C S (Δ := Δ) uv) = 0 := by
  have hp : ∀ {Δ' : List PT}, compLitSize (samplePrin2C S (Δ := Δ')) = 0 := by
    intro Δ'; unfold samplePrin2C; split_ifs <;>
      simp [bindV, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize]
  have hs : ∀ {Δ' : List PT}, compLitSize (sampleSpkPair2C S (Δ := Δ')) = 0 := by
    intro Δ'; unfold sampleSpkPair2C; split_ifs <;>
      simp [bindV, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize]
  have ho : ∀ {Δ' : List PT}, compLitSize (sampleOpkTriple2C S (Δ := Δ')) = 0 := by
    intro Δ'; unfold sampleOpkTriple2C; split_ifs <;>
      simp [bindV, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize]
  have hso : ∀ {Δ' : List PT}, compLitSize (sampleSendOpkTarget2C S (Δ := Δ')) = 0 := by
    intro Δ'; unfold sampleSendOpkTarget2C; split_ifs <;>
      simp [bindV, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize]
  have hsno : ∀ {Δ' : List PT}, compLitSize (sampleSendNoOpkTarget2C S (Δ := Δ')) = 0 := by
    intro Δ'; unfold sampleSendNoOpkTarget2C; split_ifs <;>
      simp [bindV, gPrim, liftBase, sIndex, v, compLitSize, exprLitSize]
  have hst : ∀ {Δ' : List PT}, compLitSize (sampleSendTarget2C S (Δ := Δ')) = 0 := by
    intro Δ'; unfold sampleSendTarget2C
    split_ifs
    · rfl
    · exact k1_chooseArm2C_litSize (Γ₁ := Δ') _ _ _ _ hso hsno
  unfold initParams1Key2C
  split_ifs
  · simp [pa2Mk, v, compLitSize, exprLitSize]
  · refine k1_chooseArm2C_litSize _ _ _ _ ?_ ?_
    · intro Δ' _; refine k1_chooseArm2C_litSize _ _ _ _ ?_ ?_ <;>
        (intro Δ'' _; simp [pa2Mk, bindV, v, compLitSize, exprLitSize, hp, hs, hst])
    · intro Δ' _; refine k1_chooseArm2C_litSize _ _ _ _ ?_ ?_ <;>
        (intro Δ'' _; simp [pa2Mk, bindV, v, compLitSize, exprLitSize, hp, hst, hso, ho])

set_option linter.unusedSimpArgs false in
private theorem k1_fgKeyInd1KeyGapDh2Prog_litSize_le (S : Setup) (K : Nat) :
    red1LitSize (fgKeyInd1KeyGapDh2Prog S K) ≤ 35000 := by
  have hGH := k1_gdhHandle2_litSize_le S K
  have hGF := k1_gdhFinish2_litSize_le S K
  have hH : compLitSize (gdh1KeyHandle2 S K) ≤ 30600 := by
    simp only [gdh1KeyHandle2, initPrin1Key2B,
      genSpk1Key2B, k1_callGdhHandle2_litSize,
      pa2Up, pa2PrinTarget, pa2V, pa2SpkTarget, eCaseOpt,
      smBase, smFgL, smRaw, smLog, smPows, smMk, smUpd,
      stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stSecb, stMk, stUpd,
      peSecIKA0, peIkAPk, peSecIKAsign, peIkSignPk, peCorrupted, peMk,
      sbSpkSk, sbSpkPk, sbSpkSig, sbPqspkSk, sbPqspkPk, sbPqspkSig, sbRevealed, sbMk,
      buIkB, buSpkId, buSpkB, buSpkSig, buOpkB, buPqspkId, buPqspkB, buPqspkSig, buMk,
      rNone, rInitPrin, rBundle, natEq, nat2Eq, encEC, encKEM, consB,
      letV, bindV, caseOptV, caseSumV, eAny, eFind,
      k1_liftGdhComp_litSize, liftGdhComp, k1_gPrim_litSize, gPrim, liftBase, sigChalQ_dsl,
      sBytes32, sRandom64, qX25519Base, qKemKeyGen,
      litB, u32OfNat, v, compLitSize, exprLitSize, pqOpLitSize,
      List.length_nil, List.length_cons, Nat.add_zero, Nat.zero_add]
    generalize compLitSize (gdhHandle2 S K) = cGH at hGH ⊢
    omega
  have hF : compLitSize (gdh1KeyFinish2 S K) ≤ 1000 := by
    simp only [gdh1KeyFinish2, letV, v, compLitSize, exprLitSize,
      k1_renameComp_litSize, k1_liftGdhComp_litSize, Nat.add_zero, Nat.zero_add]
    generalize compLitSize (gdhFinish2 S K) = cGF at hGF ⊢
    omega
  have hI : compLitSize (fgKeyInd1KeyGapDh2Prog S K).init ≤ 100 := by
    dsimp only [fgKeyInd1KeyGapDh2Prog]
    simp only [initAdv4_1Key2, initAdv4_1Key2Base, k1_initParams1Key2C_litSize,
      emptySimE, smMk, emptyStE, stMk,
      letV, bindV, k1_liftGdhComp_litSize, k1_gPrim_litSize, gPrim, liftBase,
      sBool, v, compLitSize, exprLitSize, Nat.add_zero, Nat.zero_add]
    omega
  have hEq : red1LitSize (fgKeyInd1KeyGapDh2Prog S K) =
      compLitSize (fgKeyInd1KeyGapDh2Prog S K).init + compLitSize (gdh1KeyHandle2 S K) +
      compLitSize (gdh1KeyFinish2 S K) := rfl
  rw [hEq]
  generalize compLitSize (fgKeyInd1KeyGapDh2Prog S K).init = cI at hI ⊢
  generalize compLitSize (gdh1KeyHandle2 S K) = cH at hH ⊢
  generalize compLitSize (gdh1KeyFinish2 S K) = cF at hF ⊢
  omega

end OneKeySizeBounds

section K1TightHandleCost

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.LegacyCosted
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd hiding bits_0 bits_1 bits_2 bits_3 bits_32
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh

private theorem k1_letV_gdh_cost_add_le {Γ : List PT} {τ₁ τ₂ : PT}
    (e : Expr pqxdhOps Γ τ₁) (he : e.cost ≤ 2)
    (k : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ₂)
    {d c : ℕ} (hk : (k .zero).cost + (d + 4) ≤ c) :
    (letV e k).cost + d ≤ c := by
  simp only [letV, Comp.cost]
  omega

private theorem k1_caseSumV_gdh_cost_add_le {Γ : List PT} {τ₁ τ₂ τ : PT}
    (x : Var Γ (.sum τ₁ τ₂))
    (kl : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps pqGapDhIface (τ₁ :: Γ) τ)
    (kr : Var (τ₂ :: Γ) τ₂ → Comp pqxdhOps pqGapDhIface (τ₂ :: Γ) τ)
    {d c : ℕ} (hl : (kl .zero).cost + (d + 2) ≤ c) (hr : (kr .zero).cost + (d + 2) ≤ c) :
    (caseSumV (v x) kl kr).cost + d ≤ c := by
  simp only [caseSumV, v, Comp.cost, Expr.cost]
  omega

private theorem k1_arm_cost_le {Γ : List PT} {τ : PT}
    (m : Comp pqxdhOps pqGapDhIface Γ τ) {d c : ℕ}
    (hub : m.costUB + d ≤ c) : m.cost + d ≤ c :=
  (Nat.add_le_add_right m.cost_le_costUB d).trans hub

private theorem k1_wrapBase2_costUB {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pa : Var Γ₁ params2Ty) (sm : Var Γ₂ simTy)
    (c : Comp pqxdhOps pqPrimIface Δ (.prod keyIndRespTy keyIndStateTy)) :
    (wrapBase2 pa sm c).costUB = c.costUB + 30 := by
  simp only [wrapBase2, smUpd, smMk, bindV_costUB, gPrim_costUB,
    smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, v_costUB, Comp.costUB, Expr.costUB]

private theorem k1_wrapSim2_costUB {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
    (pa : Var Γ₁ params2Ty)
    (c : Comp pqxdhOps pqGapDhIface Δ (.prod keyIndRespTy simTy)) :
    (wrapSim2 pa c).costUB = c.costUB + 9 := rfl

set_option maxRecDepth 100000 in
private theorem k1_gdhHandle2_cost_tight (S : Setup) (K : Nat) :
    (gdhHandle2 S K).cost ≤
      20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30000 := by
  unfold gdhHandle2
  refine Nat.le_of_add_right_le (k := 0) ?_
  refine k1_letV_gdh_cost_add_le _ (by simp [v, Expr.cost]) _ ?_
  refine k1_letV_gdh_cost_add_le _ (by simp [v, Expr.cost]) _ ?_
  refine k1_letV_gdh_cost_add_le _ (by simp [smBase, v, Expr.cost]) _ ?_
  refine k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ (k1_caseSumV_gdh_cost_add_le _ _ _ ?_
    (k1_caseSumV_gdh_cost_add_le _ _ _ ?_ ?_)))))))))))) <;> (
    refine k1_arm_cost_le _ ?_
    simp only [initPrinGdh2B, corruptB, genSpkGdh2B, genOpkGdh2B,
      initiateGdh2B, finishAcceptGdhC_costUB, acceptOpkGdh2B, acceptNoOpkGdhB,
      testB, roParsedC, roRawFallbackC, revealB, registerGdhB, revealSpkB,
      k1_wrapBase2_costUB, k1_wrapSim2_costUB,
      pa2U, pa2V, pa2Up, pa2PrinTarget, pa2DhFlag,
      pa2EphTarget, pa2SpkTarget, pa2OpkMode, pa2OpkTarget, ephSidMatchesE,
      stMk, stUpd, peMk, peUpd, sbMk, sbUpd, oeMk, oeUpd, buMk, hdMk, seMk, seUpd, reUpd,
      smMk, smUpd, qKJO, rs, slice32_costUB,
      qK_costUB, qJ_costUB, qO_costUB, qHdr_costUB,
      rNone_costUB, rInitPrin_costUB, rPk_costUB, rCorr_costUB, rBundle_costUB, rHdr_costUB,
      rInitUnfresh_costUB, rDrKey_costUB, rSpkSk_costUB,
      smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      initSidE, natEq, nat2Eq, nat3Eq, sidEq, kyberEq, kyberCheckE, freshE,
      optU32Eq, isSomeE, optFst, optSnd, nonZero32, encEC_costUB, encKEM_costUB,
      eLet2, reMk,
      letV_costUB, bindV_costUB, caseOptV_costUB,
      eLet_costUB, eCaseOpt_costUB, eCaseSum_costUB, eFind_costUB, eAny_costUB, eMap_costUB,
      gPrim_costUB, koskBundleOkPowsC_costUB, koskSenderOkPowsC_costUB,
      resolveSigPkC_costUB, lookupSpkSkC_costUB, honestPeerC_costUB, checkProvC_costUB,
      findHonestC_costUB, chooseInitRandC_costUB,
      computePosC_costUB, computeOptPosInitC_costUB, mkSecretPosC_costUB, fgPatchC_costUB,
      sBytes32_costUB, sRandom64_costUB, sDrKey96_costUB,
      qX25519_costUB, qX25519Base_costUB, qIsCanonical_costUB, qPow8_costUB,
      qSigPkGen_costUB, qSigSign_costUB, qSigVerify_costUB,
      qKemKeyGen_costUB, qKemEncaps_costUB, qKemDecaps_costUB,
      litB_costUB, takeKB_costUB, lenB_costUB, eqB_costUB,
      u32OfNat_costUB, eqU32_costUB, v_costUB,
      Comp.costUB, Expr.costUB,
      List.length_nil, List.length_replicate, F_X25519_length', PNat.val_ofNat,
      bits_32, bits_64, bits_96, bits_128, bits_160, bits_192,
      ↓reduceIte, Bool.false_eq_true]
    omega)

private theorem k1_bernoulliRatioGdhC_costUB_le {Δ : List PT} (A B : Nat) :
    (bernoulliRatioGdhC (Δ := Δ) A B).costUB ≤
      if A = 0 ∨ B = 0 then 2 else 3 * bits (A + B) + 25 := by
  unfold bernoulliRatioGdhC
  by_cases hA : A = 0
  · simp [hA, Comp.costUB, Expr.costUB]
  by_cases hB : B = 0
  · simp [hA, hB, Comp.costUB, Expr.costUB]
  simp only [hA, hB, or_self, ↓reduceIte]
  split_ifs
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : bits A ≤ bits (A + B) := bits_mono (by omega)
    omega
  · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB, bits_1]
    have hm : bits B ≤ bits (A + B) := bits_mono (by omega)
    omega

private theorem k1_chooseArm2C_cost_le {Γ₁ Δ : List PT} [Ext Γ₁ Δ] {τ : PT} (A B : Nat)
    (c1 c2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], Comp pqxdhOps pqGapDhIface Δ' τ)
    (M : Nat) (_hN : A + B ≠ 0)
    (h1 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c1 (Δ' := Δ')).cost ≤ M)
    (h2 : ∀ {Δ' : List PT} [Ext Γ₁ Δ'], (c2 (Δ' := Δ')).cost ≤ M) :
    (chooseArm2C (Γ₁ := Γ₁) (Δ := Δ) A B c1 c2).cost ≤ 3 * bits (A + B) + M + 30 := by
  rw [chooseArm2C]
  by_cases hw1 : A = 0
  · simp only [hw1, ↓reduceIte]; exact h2.trans (by omega)
  · by_cases hw2 : B = 0
    · simp only [hw1, hw2, ↓reduceIte]; exact h1.trans (by omega)
    · simp only [hw1, hw2, ↓reduceIte, bindV, v, Comp.cost, Expr.cost]
      have hb := (bernoulliRatioGdhC (Δ := Δ) A B).cost_le_costUB.trans
        (k1_bernoulliRatioGdhC_costUB_le (Δ := Δ) A B)
      simp only [hw1, hw2, or_self, ↓reduceIte] at hb
      have hc1 := h1 (Δ' := .bool :: Δ); have hc2 := h2 (Δ' := .bool :: Δ); omega

private theorem k1_coordSamplers2_costUB_le (S : Setup) {Δ : List PT} :
    (samplePrin2C S (Δ := Δ)).costUB ≤ bits S.N_dh + 10 ∧
    (sampleSpkPair2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 15 ∧
    (sampleOpkTriple2C S (Δ := Δ)).costUB ≤ 3 * bits S.N_dh + 20 ∧
    (sampleSendOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 20 ∧
    (sampleSendNoOpkTarget2C S (Δ := Δ)).costUB ≤ 2 * bits S.N_dh + 20 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold samplePrin2C; split_ifs
    · simp [Comp.costUB, Expr.costUB]
    · simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega); omega
  · unfold sampleSpkPair2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_recv) (b := S.N_dh) (by omega); omega
  · unfold sampleOpkTriple2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hSpk : 0 < S.N_spk_tot := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_opk_tot, hc])
      have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => Nat.ne_of_gt hSpk (by simp [Setup.N_spk_tot, hc])
      have hR : S.N_recv ≤ S.N_spk_tot := Nat.le_mul_of_pos_left _ hId
      have hO : S.N_opk ≤ S.N_opk_tot := Nat.le_mul_of_pos_left _ hSpk
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_recv) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_opk) (b := S.N_dh) (by omega); omega
  · unfold sampleSendOpkTarget2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_opk_tot, hc])
      have hS : S.N_send_opk ≤ S.N_send_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_send_opk) (b := S.N_dh) (by omega); omega
  · unfold sampleSendNoOpkTarget2C; split_ifs with h0
    · simp [Comp.costUB, Expr.costUB]
    · have hId : 0 < S.N_id := Nat.pos_of_ne_zero fun hc => h0 (by simp [Setup.N_send_no_opk_tot, hc])
      have hS : S.N_send_no_opk ≤ S.N_send_no_opk_tot := Nat.le_mul_of_pos_left _ hId
      simp only [bindV_costUB, gPrim_costUB, sIndex_costUB, v_costUB, Comp.costUB, Expr.costUB]
      have := bits_mono (a := S.N_id) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_send_no_opk_tot) (b := S.N_dh) (by omega)
      have := bits_mono (a := S.N_send_no_opk) (b := S.N_dh) (by omega); omega

private theorem k1_sampleSendTarget2C_cost_le (S : Setup) {Δ : List PT} :
    (sampleSendTarget2C S (Δ := Δ)).cost ≤ 5 * bits S.N_dh + 60 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  unfold sampleSendTarget2C; split_ifs with h0
  · simp [Comp.cost, Expr.cost]
  · have hb := k1_chooseArm2C_cost_le (Γ₁ := Δ) (Δ := Δ) S.N_send_opk_tot S.N_send_no_opk_tot
      _ _ (2 * bits S.N_dh + 20) (by omega)
      (fun {Δ'} [_] => (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.1)
      (fun {Δ'} [_] => (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := Δ')).2.2.2.2)
    have bm : bits (S.N_send_opk_tot + S.N_send_no_opk_tot) ≤ bits S.N_dh := bits_mono (by omega)
    omega

private theorem k1_fgKeyInd1KeyGapDh2Prog_init_cost_le (S : Setup) (K : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).init.cost ≤ 22 * bits S.N_dh + K + 320 := by
  have hfg : _root_.SignalPqxdh.Security.fgTotalIndexCount S =
      S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
      S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot := rfl
  have hs : S.N_send_tot = S.N_send_opk_tot + S.N_send_no_opk_tot := rfl
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hsq : ∀ x, x ≤ S.N_dh * S.N_dh → bits x ≤ 2 * bits S.N_dh + 1 := fun x hx =>
    le_trans (bits_mono hx) (by have hm := bits_mul S.N_dh S.N_dh; omega)
  have hInitP : ∀ {Γ₁ Δ : List PT} [Ext Γ₁ Δ]
      (uv : Var Γ₁ (.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32))),
      (initParams1Key2C S (Δ := Δ) uv).cost ≤ 19 * bits S.N_dh + 220 := by
    intro Γ₁ Δ _ uv; unfold initParams1Key2C; split_ifs with h0
    · simp only [pa2Mk, v, Comp.cost, Expr.cost, bits_0, bits_3]; omega
    · refine (k1_chooseArm2C_cost_le _ _ _ _ (13 * bits S.N_dh + 150) (by omega) ?_ ?_).trans ?_
      · intro Δ₁ _
        by_cases hAC : S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot = 0
        · have hA0 : S.N_id * S.N_spk_tot = 0 := by omega
          simp only [chooseArm2C, hA0, ↓reduceIte, bindV, pa2Mk,
            v, Comp.cost, Expr.cost, bits_1]
          have h1 := k1_sampleSendTarget2C_cost_le S (Δ := Δ₁)
          have h2 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₁)).2.1
          omega
        · refine (k1_chooseArm2C_cost_le _ _ _ _ (7 * bits S.N_dh + 110) hAC ?_ ?_).trans ?_
          · intro Δ₂ _; simp only [bindV, pa2Mk, v, Comp.cost, Expr.cost, bits_0]
            have h1 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := Δ₂)).1
            have h2 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := .opt .nat :: Δ₂)).2.1
            omega
          · intro Δ₂ _; simp only [bindV, pa2Mk, v, Comp.cost, Expr.cost, bits_1]
            have h1 := k1_sampleSendTarget2C_cost_le S (Δ := Δ₂)
            have h2 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₂)).2.1
            omega
          · have bsum := hsq (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot) (by nlinarith); omega
      · intro Δ₁ _
        by_cases hBD : S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot = 0
        · have hB0 : S.N_send_tot * S.N_id = 0 := by omega
          simp only [chooseArm2C, hB0, ↓reduceIte, bindV, pa2Mk,
            v, Comp.cost, Expr.cost, bits_3]
          have h1 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := Δ₁)).2.2.2.1
          have h2 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₁)).2.2.1
          omega
        · refine (k1_chooseArm2C_cost_le _ _ _ _ (7 * bits S.N_dh + 110) hBD ?_ ?_).trans ?_
          · intro Δ₂ _; simp only [bindV, pa2Mk, v, Comp.cost, Expr.cost, bits_2]
            have h1 := k1_sampleSendTarget2C_cost_le S (Δ := Δ₂)
            have h2 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₂)).1
            omega
          · intro Δ₂ _; simp only [bindV, pa2Mk, v, Comp.cost, Expr.cost, bits_3]
            have h1 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := Δ₂)).2.2.2.1
            have h2 := (Comp.cost_le_costUB _).trans (k1_coordSamplers2_costUB_le S (Δ := .opt ephTargetTy :: Δ₂)).2.2.1
            omega
          · have bsum := hsq (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot)
              (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)]); omega
      · have bsum := hsq (S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
            (S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot))
          (by nlinarith [Nat.zero_le (S.N_send_no_opk_tot * S.N_opk_tot)]); omega
  have hsBool : ∀ {Δ' : List PT}, (gPrim (Γ := Δ') sBool).cost ≤ 10 := fun {Δ'} =>
    (Comp.cost_le_costUB _).trans (by simp [sBool_costUB])
  simp only [fgKeyInd1KeyGapDh2Prog, initAdv4_1Key2, initAdv4_1Key2Base, emptySimE, smMk, emptyStE, stMk,
    letV, bindV, liftGdhComp_cost, v, Comp.cost, Expr.cost]
  have hp := hInitP
    (Γ₁ := [.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32),
            .prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32)])
    (Δ := [.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32),
           .prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32)]) .zero
  have hsB := hsBool (Δ' := params2Ty ::
    [.prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32),
     .prod (SignalPqxdh.LegacyCosted.B 32) (SignalPqxdh.LegacyCosted.B 32)])
  have hbK : bits (min K (min S.N_spk_tot S.N_recv)) ≤ K + 1 :=
    (bits_mono (Nat.min_le_left _ _)).trans (bits_le_succ K)
  omega

private theorem k1_gdh1KeyHandle2_cost_tight (S : Setup) (K : Nat) :
    (gdh1KeyHandle2 S K).cost ≤
      20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30050 := by
  have hCall : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy),
      (callGdhHandle2 S K st1 q).cost ≤
        20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30020 := by
    intro Δ st1 q
    have hEq : (callGdhHandle2 S K st1 q).cost = (gdhHandle2 S K).cost + 14 := by
      simp only [callGdhHandle2, letV, bindV, v, Comp.cost, Expr.cost,
        renameComp_cost, liftGdhComp_cost]; omega
    have hH := k1_gdhHandle2_cost_tight S K
    rw [hEq]
    generalize (gdhHandle2 S K).cost = cGH at hH ⊢
    omega
  have hIp : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (st1 : Var Γ₁ gdh1KeyState2Ty) (u : Var Γ₂ .nat),
      (initPrin1Key2B K (Δ := Δ) st1 u).cost ≤ 7 * K + 450 := by
    intro Γ₁ Γ₂ Δ _ _ st1 u
    refine le_trans (initPrin1Key2B K (Δ := Δ) st1 u).cost_le_costUB ?_
    simp only [initPrin1Key2B, stPrin, stUpd, stSecb, stSpks, stOpks, stSess, stResps,
      stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peMk, smUpd, smMk,
      smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
      pa2Up, pa2PrinTarget, rNone, rInitPrin, natEq,
      letV_costUB, bindV_costUB, eCaseOpt_costUB, eAny_costUB, liftGdhComp_costUB, gPrim_costUB,
      sBytes32_costUB, qX25519Base_costUB, litB_costUB, v_costUB,
      Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat]; omega
  have hGs : ∀ {Δ : List PT} (st1 : Var Δ gdh1KeyState2Ty) (q : Var Δ keyIndQueryTy)
      (x : Var Δ (.prod .nat .nat)),
      (genSpk1Key2B S K st1 q x).cost ≤
        20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30040 := by
    intro Δ st1 q x
    let arm : Comp pqxdhOps pqSigAndDdhIface Δ (.prod keyIndRespTy gdh1KeyState2Ty) :=
      let pa := Expr.fst (.fst (v st1))
      letV pa fun paV => letV (.snd (.fst (v st1))) fun sm => letV (smBase (v sm)) fun bSt =>
      letV (.snd (v st1)) fun sigB =>
      .ite (eAny K (stSpks (v bSt)) fun p => nat2Eq (.fst (v p)) (v x)) (.ret (.pair rNone (v st1)))
        (caseOptV (eFind K (stPrin (v bSt)) fun p => natEq (.fst (v p)) (.fst (v x)))
          (.ret (.pair rNone (v st1))) fun ue =>
          .ite (natEq (v sigB) (.nat 0)) (.ret (.pair rNone (v st1)))
            (letV (eCaseOpt (pa2SpkTarget (v paV)) (.bool false) fun sp => nat2Eq (v x) (v sp)) fun isT =>
             bindV (liftGdhComp (gPrim sBytes32)) fun spkSkRaw =>
             bindV (liftGdhComp (gPrim (qX25519Base (v spkSkRaw)))) fun spkPkRaw =>
             letV (.ite (v isT) (litB 32 []) (v spkSkRaw)) fun spkSk =>
             letV (.ite (v isT) (pa2V (v paV)) (v spkPkRaw)) fun spkPk =>
             bindV (sigChalQ_dsl 33 (encEC (v spkPk))) fun spkSig =>
             bindV (liftGdhComp (gPrim sRandom64)) fun seed =>
             bindV (liftGdhComp (gPrim (qKemKeyGen (v seed)))) fun kp =>
             bindV (sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun pqSig =>
             let jId := u32OfNat (.snd (v x))
             let bE := sbMk (v spkSk) (v spkPk) (v spkSig) (.snd (v kp)) (.fst (v kp)) (v pqSig) (.bool false)
             let buOut := buMk (peIkAPk (.snd (v ue))) jId (v spkPk) (v spkSig) .none jId (.fst (v kp)) (v pqSig)
             let bSt' := stUpd (v bSt) (spks := .cons (.pair (v x) bE) (stSpks (v bSt)))
             let sm' := smUpd (v sm) (base := bSt')
             .ret (.pair (rBundle buOut) (.pair (.pair (v paV) sm') (.sub (v sigB) (.nat 1))))))
    have hArm : arm.cost ≤ 20 * K + 9000 := by
      refine le_trans arm.cost_le_costUB ?_
      simp only [arm, stPrin, stSpks, stUpd, stSecb, stOpks, stSess, stResps,
        stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, peIkAPk, sbMk, buMk, smUpd, smMk,
        smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB,
        pa2V, pa2SpkTarget, rNone, rBundle, natEq, nat2Eq, encEC_costUB, encKEM_costUB,
        letV_costUB, bindV_costUB, caseOptV_costUB, eCaseOpt_costUB, eAny_costUB, eFind_costUB,
        liftGdhComp_costUB, gPrim_costUB, sigChalQ_dsl_costUB, sBytes32_costUB, sRandom64_costUB,
        qX25519Base_costUB, qKemKeyGen_costUB, litB_costUB, u32OfNat_costUB, v_costUB,
        Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]; omega
    have hEq : genSpk1Key2B S K st1 q x =
        .ite (eCaseOpt (pa2PrinTarget (.fst (.fst (v st1)))) (.bool false) fun uT => natEq (.fst (v x)) (v uT))
          arm (callGdhHandle2 S K st1 q) := rfl
    rw [hEq]; have hc := hCall st1 q
    simp only [Comp.cost, eCaseOpt, pa2PrinTarget, natEq, v, Expr.cost]
    generalize arm.cost = cArm at hArm ⊢
    generalize (callGdhHandle2 S K st1 q).cost = cCall at hc ⊢
    omega
  have step : ∀ {a b m₁ m₂ n : Nat}, a ≤ m₁ → b ≤ m₂ → m₁ + 2 ≤ n → m₂ + 2 ≤ n →
      1 + max a b + 1 ≤ n :=
    fun _ _ _ _ => by omega
  unfold gdh1KeyHandle2
  simp only [caseSumV, v, Comp.cost, Expr.cost]
  refine step (m₂ := 20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30044)
    (hIp _ _) ?_ (by omega) (by omega)
  refine step (m₂ := 20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30042)
    (hCall _ _) ?_ (by omega) (by omega)
  exact step (hGs _ _ _) (hCall _ _) (by omega) (by omega)

private theorem k1_gdh1KeyFinish2_cost_le_min (S : Setup) (K : Nat) :
    (gdh1KeyFinish2 S K).cost ≤
      69 * (min K S.N_dh * min K S.N_dh) + 69 * (K * min K S.N_dh) +
        66 * (min K S.N_dh * min K S.N_sess_tot) +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot + 2132 * K + 420 := by
  have hF : (gdhFinish2 S K).cost ≤
      69 * (min K S.N_dh * min K S.N_dh) + 69 * (K * min K S.N_dh) +
        66 * (min K S.N_dh * min K S.N_sess_tot) +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot + 2132 * K + 409 := by
    refine le_trans (gdhFinish2 S K).cost_le_costUB ?_
    simp only [gdhFinish2, extractMode0_2C, logFind2C, spkPowsC_costUB, findMapStep2C,
      initDh1CandC_costUB, respDh1CandC_costUB, slice32_costUB,
      smBase_costUB, smLog_costUB, smPows_costUB, pa2U, pa2V, pa2Mode,
      natEq, letV_costUB, bindV_costUB, caseOptV_costUB, findMV_costUB, foldMV_costUB,
      eCaseOpt_costUB, eMap_costUB, ddhQ_costUB, litB_costUB, v_costUB,
      Comp.costUB, Expr.costUB, List.length_replicate, PNat.val_ofNat,
      bits_0, bits_1, bits_2, bits_32, bits_64, bits_96, bits_128]
    nlinarith
  have hEq : (gdh1KeyFinish2 S K).cost = (gdhFinish2 S K).cost + 4 := by
    simp only [gdh1KeyFinish2, letV, v, Comp.cost, Expr.cost, renameComp_cost, liftGdhComp_cost]; omega
  rw [hEq]
  generalize (gdhFinish2 S K).cost = cGF at hF ⊢
  omega

private theorem k1_fgKeyInd1KeyGapDh2Prog_totalCost_tight (S : Setup) (K q : Nat) :
    (fgKeyInd1KeyGapDh2Prog S K).totalCost q ≤
      q * (20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30082) +
        69 * (min K S.N_dh * min K S.N_dh) + 69 * (K * min K S.N_dh) +
        66 * (min K S.N_dh * min K S.N_sess_tot) +
        423 * min K S.N_dh + 263 * min K S.N_sess_tot +
        22 * bits S.N_dh + 2133 * K + 760 := by
  have hI := k1_fgKeyInd1KeyGapDh2Prog_init_cost_le S K
  have hH := k1_gdh1KeyHandle2_cost_tight S K
  have hF := k1_gdh1KeyFinish2_cost_le_min S K
  have hEq : (fgKeyInd1KeyGapDh2Prog S K).totalCost q =
      (fgKeyInd1KeyGapDh2Prog S K).init.cost +
        q * max 1 ((gdh1KeyHandle2 S K).cost + 32) +
        (gdh1KeyFinish2 S K).cost := rfl
  rw [hEq]
  generalize (fgKeyInd1KeyGapDh2Prog S K).init.cost = cI at hI ⊢
  generalize (gdh1KeyHandle2 S K).cost = cH at hH ⊢
  generalize (gdh1KeyFinish2 S K).cost = cF at hF ⊢
  have hmax : max 1 (cH + 32) ≤
      20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 30082 :=
    max_le (by omega) (by omega)
  have hq := Nat.mul_le_mul_left q hmax
  omega

private theorem k1_sigKeyInd1KeyProg_totalCost_tight (S : Setup) (K q : Nat) :
    (sigKeyInd1KeyProg S K).totalCost q ≤
      q * (26612 * K + 10412 * min K S.N_dh + 10000 * min K S.N_sess_tot + 15 * bits S.N_dh + 56532) +
        2 * bits S.N_dh + 1800 := by
  have hd : S.N_dh = S.N_id + S.N_spk_tot + S.N_opk_tot + S.N_send_tot := rfl
  have hI : (sigKeyInd1KeyProg S K).init.cost ≤ 2 * bits S.N_dh + 100 := by
    refine le_trans (sigKeyInd1KeyProg S K).init.cost_le_costUB ?_
    have bId : bits S.N_id ≤ bits S.N_dh := bits_mono (by omega)
    have bSpk : bits (min K (min S.N_spk_tot S.N_recv)) ≤ bits S.N_dh :=
      (bits_mono ((Nat.min_le_right _ _).trans (Nat.min_le_left _ _))).trans (bits_mono (by omega))
    dsimp only [sigKeyInd1KeyProg]
    simp only [s1Mk, emptySimE, smMk, emptyStE, stMk,
      bindV_costUB, s1Prim_costUB, sIndex_costUB, sBool_costUB, v_costUB,
      Comp.costUB, Expr.costUB]
    omega
  have hPre : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (s : Var Γ₁ sig1KeyStTy) (qv : Var Γ₂ keyIndQueryTy),
      (sig1KeyPreDispatchC S K (Δ := Δ) s qv).cost ≤ 412 * min K S.N_dh + 6612 * K + 26000 := by
    intro Γ₁ Γ₂ Δ _ _ s qv
    refine le_trans (sig1KeyPreDispatchC S K (Δ := Δ) s qv).cost_le_costUB ?_
    simp only [sig1KeyPreDispatchC, sig1KeyInitPrinB, sig1KeyTargetGenSpkB,
      sig1KeyInitiateCheckC, extract1KeyC,
      s1Fg, s1Target, s1Pk, s1Budget, s1Forgery, s1Base, s1Mk, s1Upd,
      smBase_costUB, smFgL_costUB, smRaw_costUB, smLog_costUB, smPows_costUB, smMk, smUpd,
      stPrin, stSpks, stOpks, stSess, stResps, stUsedO, stUsedN, stKyb, stRo, stAdv, stMk, stUpd,
      peIkAPk, peMk, sbSpkPk, sbPqspkPk, sbMk,
      buIkB, buSpkB, buSpkSig, buPqspkB, buPqspkSig, buMk,
      rNone, rInitPrin, rBundle, isSomeE, natEq, nat2Eq,
      encEC_costUB, encKEM_costUB, widenEC_costUB,
      letV_costUB, bindV_costUB, caseOptV_costUB, caseSumV_costUB,
      s1Prim_costUB, honestPeerC_costUB, qSigVerify_costUB, qSigDdhSign_costUB,
      sBytes32_costUB, sRandom64_costUB, qX25519Base_costUB, qKemKeyGen_costUB,
      eCaseOpt_costUB, eAny_costUB, eFind_costUB, eqB_costUB, litB_costUB, u32OfNat_costUB,
      v_costUB, Comp.costUB, Expr.costUB, List.length_nil, PNat.val_ofNat, bits_0, bits_1]
    omega
  have hDel : ∀ {Γ₁ Γ₂ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ]
      (s : Var Γ₁ sig1KeyStTy) (qv : Var Γ₂ keyIndQueryTy),
      (delegateFgC S K (Δ := Δ) s qv).cost ≤
        20000 * K + 10000 * min K S.N_dh + 10000 * min K S.N_sess_tot + 15 * bits S.N_dh + 30400 := by
    intro Γ₁ Γ₂ Δ _ _ s qv
    have hH := k1_gdhHandle2_cost_tight S K
    have hLit : (litB (Γ := Δ) 32 []).cost ≤ 40 := by
      simp [litB, Expr.cost, pqxdhOps, pqBytesOps, Ops.sum]
    simp only [delegateFgC, pa2Zero, pa2Mk, s1Fg, s1Target, s1Pk, s1Budget, s1Forgery,
      s1Mk, s1Upd, letV, bindV, liftGdhToSigDdh_cost, Comp.rename_cost,
      v, Comp.cost, Expr.cost, bits_1]
    generalize (gdhHandle2 S K).cost = cGH at hH ⊢
    generalize (litB (Γ := Δ) 32 []).cost = cL at hLit ⊢
    omega
  have hH : (sig1KeyHandleC S K).cost ≤
      26612 * K + 10412 * min K S.N_dh + 10000 * min K S.N_sess_tot + 15 * bits S.N_dh + 56500 := by
    let s : Var [sig1KeyStTy, keyIndQueryTy] sig1KeyStTy := .zero
    let q : Var [sig1KeyStTy, keyIndQueryTy] keyIndQueryTy := .succ .zero
    have hp := hPre (Δ := [sig1KeyStTy, keyIndQueryTy]) s q
    have hd' := hDel (Δ := .unit :: (.sum S1RS .unit) :: [sig1KeyStTy, keyIndQueryTy]) s q
    simp only [sig1KeyHandleC, bindV, caseSumV, v, Comp.cost, Expr.cost]
    generalize (sig1KeyPreDispatchC S K (Δ := [sig1KeyStTy, keyIndQueryTy]) s q).cost = cPre at hp ⊢
    generalize (delegateFgC S K (Δ := .unit :: (.sum S1RS .unit) :: [sig1KeyStTy, keyIndQueryTy])
      s q).cost = cDel at hd' ⊢
    omega
  have hF := sigKeyInd1KeyProg_finish_cost_le S K
  have hEq : (sigKeyInd1KeyProg S K).totalCost q =
      (sigKeyInd1KeyProg S K).init.cost + q * max 1 ((sig1KeyHandleC S K).cost + 32) +
        (sigKeyInd1KeyProg S K).finish.cost := rfl
  rw [hEq]
  generalize (sigKeyInd1KeyProg S K).init.cost = cI at hI ⊢
  generalize (sig1KeyHandleC S K).cost = cH at hH ⊢
  generalize (sigKeyInd1KeyProg S K).finish.cost = cF at hF ⊢
  have hmax : max 1 (cH + 32) ≤
      26612 * K + 10412 * min K S.N_dh + 10000 * min K S.N_sess_tot + 15 * bits S.N_dh + 56532 :=
    max_le (by omega) (by omega)
  have hq := Nat.mul_le_mul_left q hmax
  omega

end K1TightHandleCost

/-! ## Atomic programs, syntactic bounds, and advantage equalities -/

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open _root_.SignalPqxdh
open _root_.SignalPqxdh.Costed (pqSigAndDdhIface pqPrimIface)
open _root_.SignalPqxdh.Security
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd
open _root_.SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open _root_.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
open _root_.Proofs.SignalPqxdh.Security
open Computational.Proofs.ReductionDsl.AtomicSizeHonest
open Computational.Proofs.SignalPqxdh.AtomicLift
open OracleSpec OracleComp

def sigKeyInd1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
      (PB 32) .unit .bool (.prod (PB 1569) (PB 64)) :=
  liftKeyInd1Stage tlSigDdhKeyInd S (sigKeyInd1KeyDslProg S b)

def shcrKeyInd1KeyAtomicProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqPrimIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  liftKeyInd2Stage tlPrimKeyInd S (shcrKeyInd1KeyDslProg S b)

def fgKeyInd1KeyGapDhAtomicProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqSigAndDdhIface (keyIndSpec S) (pqKeyIndCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool (PB 32) :=
  liftKeyInd1Stage tlSigDdhKeyInd S (fgKeyInd1KeyGapDhDslProg S b)

private theorem k1_liftKeyInd2Stage_totalCost_two_mul_le {ι : Type} {T : OracleSpec ι}
    {I : Iface SignalPqxdh.LegacyCosted.pqSig T} {A : AtomicIface T}
    (tl : TagLift I A) (hu : I.uCost = 1) (S : SignalPqxdh.Setup)
    {rIn ch rIn2 out : Ty SignalPqxdh.LegacyCosted.pqSig}
    (R : TwoStageCostedReduction SignalPqxdh.LegacyCosted.pqxdhOps I (SignalPqxdh.keyIndSpec S)
      (SignalPqxdh.LegacyCosted.keyIndCodec S) rIn .unit .bool ch rIn2 out) (q : ℕ) :
    2 * (liftKeyInd2Stage tl S R).totalCost q ≤
      3 * R.totalCost q +
        78 * R.totalQueries (fun _ => 0) (sampR64W tl.hsmp) q + 164 * q := by
  have hI := mapComp_cost_two_mul_le tl R.init
  have hPre := mapComp_cost_two_mul_le tl R.handlePre
  have hPost := mapComp_cost_two_mul_le tl R.handlePost
  have hDone := mapComp_cost_two_mul_le tl R.chDone
  have hRes := mapComp_cost_two_mul_le tl R.resume
  have hFin := mapComp_cost_two_mul_le tl R.finish
  have hPreC := liftKeyIndHandle_cost_le tl S R.handlePre
  have hPostC := liftKeyIndHandle_cost_le tl S R.handlePost
  have hCR : 2 * max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost ≤
      3 * max R.chDone.cost R.resume.cost +
        78 * max (R.chDone.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.resume.queries (fun _ => 0) (sampR64W tl.hsmp)) := by omega
  have hPer : 2 * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64) ≤
      3 * max 1 (max R.handlePre.cost R.handlePost.cost + 32) +
        78 * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp)) + 164 := by omega
  have hMul := Nat.mul_le_mul_left q hPer
  have hR1 : 2 * (q * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64)) =
      q * (2 * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64)) := by ring
  have hR2 : q * (3 * max 1 (max R.handlePre.cost R.handlePost.cost + 32) +
        78 * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp)) + 164) =
      3 * (q * max 1 (max R.handlePre.cost R.handlePost.cost + 32)) +
        78 * (q * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp))) + 164 * q := by ring
  rw [← hR1, hR2] at hMul
  change 2 * ((mapComp tl R.init).cost +
      q * max 1 (max (liftKeyIndHandle tl S R.handlePre).cost
        (liftKeyIndHandle tl S R.handlePost).cost + 64) +
      max (mapComp tl R.chDone).cost (mapComp tl R.resume).cost +
      (mapComp tl R.finish).cost) ≤
    3 * (R.init.cost + q * max I.uCost (max R.handlePre.cost R.handlePost.cost + 32) +
      max R.chDone.cost R.resume.cost + R.finish.cost) +
      78 * (R.init.queries (fun _ => 0) (sampR64W tl.hsmp) +
        q * max (R.handlePre.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.handlePost.queries (fun _ => 0) (sampR64W tl.hsmp)) +
        max (R.chDone.queries (fun _ => 0) (sampR64W tl.hsmp))
          (R.resume.queries (fun _ => 0) (sampR64W tl.hsmp)) +
        R.finish.queries (fun _ => 0) (sampR64W tl.hsmp)) + 164 * q
  rw [hu]
  omega

private theorem k1_two_mul_clamped_le_stepCostBudget {c : ℕ} (S : Setup) (b : QueryBudget)
    (h2 : 2 * c ≤ 131072 + 262144 * b.q_total +
      65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
      2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      131072 * (b.q_total * b.q_total) +
      65536 * (b.q_total * min b.q_total S.N_dh) +
      65536 * (b.q_total * min b.q_total S.N_sess_tot) +
      4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
      512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot)) :
    c ≤ _root_.SignalPqxdh.Security.stepCostBudget S b := by
  unfold _root_.SignalPqxdh.Security.stepCostBudget
  dsimp only
  have hEq : 2 * (2 ^ 16 * (b.q_total + 1) * (b.q_total + 1) +
      2 ^ 15 * (b.q_total + 1) * (min b.q_total S.N_dh + min b.q_total S.N_sess_tot) +
      2 ^ 10 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
      2 ^ 11 * min b.q_total S.N_dh ^ 2 +
      2 ^ 8 * min b.q_total S.N_dh * min b.q_total S.N_sess_tot) =
      131072 + 262144 * b.q_total +
        65536 * min b.q_total S.N_dh + 65536 * min b.q_total S.N_sess_tot +
        2048 * (b.q_total + 1) * (Nat.log 2 S.N_dh + Nat.log 2 S.N_sess_tot) +
        131072 * (b.q_total * b.q_total) +
        65536 * (b.q_total * min b.q_total S.N_dh) +
        65536 * (b.q_total * min b.q_total S.N_sess_tot) +
        4096 * (min b.q_total S.N_dh * min b.q_total S.N_dh) +
        512 * (min b.q_total S.N_dh * min b.q_total S.N_sess_tot) := by ring
  exact Nat.le_of_mul_le_mul_left (h2.trans_eq hEq.symm) (by omega)

theorem sigKeyInd1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine k1_two_mul_clamped_le_stepCostBudget S b ?_
  have hLift := liftKeyInd1Stage_totalCost_two_mul_le tlSigDdhKeyInd rfl S
    (sigKeyInd1KeyDslProg S b) b.q_total
  have hCost := k1_sigKeyInd1KeyProg_totalCost_tight S b.q_total b.q_total
  have hR64 := sigKeyInd1KeyProg_r64_le S b.q_total b.q_total
  dsimp only [sigKeyInd1KeyAtomicProg, sigKeyInd1KeyDslProg] at hLift ⊢
  have hbits : _root_.ReductionDsl.bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  rw [hbits] at hCost
  set q := b.q_total
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hExp : q * (26612 * q + 10412 * md + 10000 * ms + 15 * (ld + 1) + 56532) =
      26612 * (q * q) + 10412 * (q * md) + 10000 * (q * ms) + 15 * (q * ld) + 56547 * q := by ring
  rw [hExp] at hCost
  have hLog : 45 * (q * ld) + 6 * ld ≤ 2048 * (q + 1) * (ld + ls) := by
    have h1 : 45 * (q * ld) + 6 * ld ≤ 45 * (q + 1) * ld := by
      have : 45 * (q + 1) * ld = 45 * (q * ld) + 45 * ld := by ring
      omega
    have h2 : 45 * (q + 1) * ld ≤ 2048 * (q + 1) * (ld + ls) :=
      Nat.mul_le_mul (Nat.mul_le_mul_right (q + 1) (show 45 ≤ 2048 by decide))
        (Nat.le_add_right ld ls)
    exact h1.trans h2
  generalize (liftKeyInd1Stage tlSigDdhKeyInd S (sigKeyInd1KeyProg S q)).totalCost q = cL at hLift ⊢
  generalize (sigKeyInd1KeyProg S q).totalCost q = cD at hLift hCost
  generalize (sigKeyInd1KeyProg S q).totalQueries (fun _ => 0) (sampR64W tlSigDdhKeyInd.hsmp) q = cQ at hLift hR64
  omega

theorem shcrKeyInd1KeyAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine k1_two_mul_clamped_le_stepCostBudget S b ?_
  have hLift := k1_liftKeyInd2Stage_totalCost_two_mul_le tlPrimKeyInd rfl S
    (shcrKeyInd1KeyDslProg S b) b.q_total
  have hTwo := shcrKeyInd1KeyProg_totalCost_le_twoKey S b.q_total (keyIndLoopBound b) b.q_total
  have hR64 := shcrKeyInd1KeyProg_r64_le S b.q_total (keyIndLoopBound b) b.q_total
  dsimp only [shcrKeyInd1KeyAtomicProg, shcrKeyInd1KeyDslProg] at hLift ⊢
  set q := b.q_total
  set K := keyIndLoopBound b
  have hKB : K = 2 * q + 1 := rfl
  have hPre := shcrKeyIndProg_handlePre_cost_tight_le S q K
  have hPost := shcrKeyIndProg_handlePost_cost_tight_le S q K
  have hRes := shcrKeyIndProg_resume_cost S q K
  have hFin := shcrKeyIndProg_finish_cost S q K
  have hInit := shcrKeyIndProg_init_cost_le S q K
  have hDone := shcrKeyIndProg_chDone_cost S q K
  have hu : SignalPqxdh.LegacyCosted.pqPrimIface.uCost = 1 := rfl
  have hc : (SignalPqxdh.LegacyCosted.keyIndCodec S).codecCost = 32 := rfl
  generalize (liftKeyInd2Stage tlPrimKeyInd S (shcrKeyInd1KeyProg S q K)).totalCost q = cL at hLift ⊢
  generalize (shcrKeyInd1KeyProg S q K).totalCost q = cD at hLift hTwo
  generalize (shcrKeyInd1KeyProg S q K).totalQueries (fun _ => 0) (sampR64W tlPrimKeyInd.hsmp) q = cQ at hLift hR64
  rw [TwoStageCostedReduction.totalCost, hu, hc, hFin, hDone] at hTwo
  generalize (shcrKeyIndProg S q K).handlePre.cost = cPre at hTwo hPre
  generalize (shcrKeyIndProg S q K).handlePost.cost = cPost at hTwo hPost
  generalize (shcrKeyIndProg S q K).resume.cost = cRes at hTwo hRes
  generalize (shcrKeyIndProg S q K).init.cost = cInit at hTwo hInit
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hmd : min K S.N_dh ≤ 2 * md + 1 := by omega
  have hms : min K S.N_sess_tot ≤ 2 * ms + 1 := by omega
  have hMaxH : max 1 (max cPre cPost + 32) ≤
      43039 + 17608 * md + 14724 * ms + 8126 * q := by omega
  have hMul := Nat.mul_le_mul_left q hMaxH
  have hExp : q * (43039 + 17608 * md + 14724 * ms + 8126 * q) =
      43039 * q + 17608 * (q * md) + 14724 * (q * ms) + 8126 * (q * q) := by ring
  rw [hExp] at hMul
  have hLog : 9 * ld ≤ 2048 * (q + 1) * (ld + ls) := by
    have h1 : 9 ≤ 2048 * (q + 1) := by omega
    exact Nat.mul_le_mul h1 (Nat.le_add_right _ _)
  omega

theorem fgKeyInd1KeyGapDhAtomicProg_totalCost_le_stepCostBudget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhAtomicProg S b).totalCost b.q_total ≤
      _root_.SignalPqxdh.Security.stepCostBudget S b := by
  refine k1_two_mul_clamped_le_stepCostBudget S b ?_
  have hLift := liftKeyInd1Stage_totalCost_two_mul_le tlSigDdhKeyInd rfl S
    (fgKeyInd1KeyGapDhDslProg S b) b.q_total
  have hCost := k1_fgKeyInd1KeyGapDh2Prog_totalCost_tight S b.q_total b.q_total
  have hR64 := fgKeyInd1KeyGapDh2Prog_r64_le S b.q_total b.q_total
  dsimp only [fgKeyInd1KeyGapDhAtomicProg, fgKeyInd1KeyGapDhDslProg] at hLift ⊢
  have hbits : _root_.ReductionDsl.bits S.N_dh = Nat.log 2 S.N_dh + 1 := rfl
  rw [hbits] at hCost
  set q := b.q_total
  set md := min b.q_total S.N_dh
  set ms := min b.q_total S.N_sess_tot
  set ld := Nat.log 2 S.N_dh
  set ls := Nat.log 2 S.N_sess_tot
  have hExp : q * (20000 * q + 10000 * md + 10000 * ms + 30082) =
      20000 * (q * q) + 10000 * (q * md) + 10000 * (q * ms) + 30082 * q := by ring
  rw [hExp] at hCost
  have hLog : 66 * ld ≤ 2048 * (q + 1) * (ld + ls) := by
    have h1 : 66 ≤ 2048 * (q + 1) := by omega
    exact Nat.mul_le_mul h1 (Nat.le_add_right _ _)
  generalize (liftKeyInd1Stage tlSigDdhKeyInd S (fgKeyInd1KeyGapDh2Prog S q)).totalCost q = cL at hLift ⊢
  generalize (fgKeyInd1KeyGapDh2Prog S q).totalCost q = cD at hLift hCost
  generalize (fgKeyInd1KeyGapDh2Prog S q).totalQueries (fun _ => 0) (sampR64W tlSigDdhKeyInd.hsmp) q = cQ at hLift hR64
  omega

theorem sigKeyInd1KeyAtomicProg_sigQueries_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyAtomicProg S b).totalQueries
      chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total :=
  (liftKeyInd1Stage_totalQueries_le tlSigDdhKeyInd S
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW
    (sigKeyInd1KeyDslProg S b) b.q_total).trans
    (sigKeyInd1KeyDslProg_sigQueries_le S b)

theorem sigKeyInd1KeyAtomicProg_ddhQueries_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyAtomicProg S b).totalQueries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot :=
  (liftKeyInd1Stage_totalQueries_le tlSigDdhKeyInd S
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW
    (sigKeyInd1KeyDslProg S b) b.q_total).trans
    (sigKeyInd1KeyDslProg_ddhQueries_le S b)

theorem sigKeyInd1KeyAtomicProg_primQueries_le (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyAtomicProg S b).totalQueries
      chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b :=
  (liftKeyInd1Stage_totalQueries_le tlSigDdhKeyInd S
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    chalIfacePrimQueryWeight tlSigDdhKeyInd_primW
    (sigKeyInd1KeyDslProg S b) b.q_total).trans
    (sigKeyInd1KeyDslProg_primQueries_le S b)

theorem shcrKeyInd1KeyAtomicProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyAtomicProg S b).totalQueries
      primIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b :=
  (liftKeyInd2Stage_totalQueries_le tlPrimKeyInd S
    SignalPqxdh.LegacyCosted.primIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    primIfacePrimQueryWeight tlPrimKeyInd_primW
    (shcrKeyInd1KeyDslProg S b) b.q_total).trans
    (shcrKeyInd1KeyDslProg_totalPrimQueries_le S b)

theorem fgKeyInd1KeyGapDhAtomicProg_totalSigQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhAtomicProg S b).totalQueries
      chalIfaceSigQueryWeight samplerZeroQueryWeight b.q_total ≤ 2 * b.q_total := by
  dsimp only [fgKeyInd1KeyGapDhAtomicProg, fgKeyInd1KeyGapDhDslProg]
  exact (liftKeyInd1Stage_totalQueries_le tlSigDdhKeyInd S
    SignalPqxdh.LegacyCosted.chalIfaceSigQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    chalIfaceSigQueryWeight tlSigDdhKeyInd_sigW
    (fgKeyInd1KeyGapDh2Prog S b.q_total) b.q_total).trans
    (fgKeyInd1KeyGapDh2Prog_totalSigQueries_le S b)

theorem fgKeyInd1KeyGapDhAtomicProg_totalDdhQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhAtomicProg S b).totalQueries
      chalIfaceDdhQueryWeight samplerZeroQueryWeight b.q_total ≤
      4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot := by
  dsimp only [fgKeyInd1KeyGapDhAtomicProg, fgKeyInd1KeyGapDhDslProg]
  exact (liftKeyInd1Stage_totalQueries_le tlSigDdhKeyInd S
    SignalPqxdh.LegacyCosted.chalIfaceDdhQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    chalIfaceDdhQueryWeight tlSigDdhKeyInd_ddhW
    (fgKeyInd1KeyGapDh2Prog S b.q_total) b.q_total).trans
    (fgKeyInd1KeyGapDh2Prog_totalDdhQueries_le S b)

theorem fgKeyInd1KeyGapDhAtomicProg_totalPrimQueries_le (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhAtomicProg S b).totalQueries
      chalIfacePrimQueryWeight samplerZeroQueryWeight b.q_total ≤ primQueryBudget S b := by
  dsimp only [fgKeyInd1KeyGapDhAtomicProg, fgKeyInd1KeyGapDhDslProg]
  exact (liftKeyInd1Stage_totalQueries_le tlSigDdhKeyInd S
    SignalPqxdh.LegacyCosted.chalIfacePrimQueryWeight
    SignalPqxdh.LegacyCosted.samplerZeroQueryWeight
    chalIfacePrimQueryWeight tlSigDdhKeyInd_primW
    (fgKeyInd1KeyGapDh2Prog S b.q_total) b.q_total).trans
    (fgKeyInd1KeyGapDh2Prog_totalPrimQueries_le S b)

theorem sigKeyInd1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (sigKeyInd1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hLift := liftKeyInd1Stage_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe S (sigKeyInd1KeyDslProg S b)
  have hSz := sigKeyInd1KeyDslProg_size_le_stepCostBudget S b
  dsimp only [sigKeyInd1KeyAtomicProg, sigKeyInd1KeyDslProg] at hLift hSz ⊢
  have hLit := k1_sigKeyInd1KeyProg_litSize_le S b.q_total
  have h0 : 205402 ≤ _root_.ReductionDsl.reductionSizeBudget := by decide
  have h1 : 1250 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ≤
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    Nat.mul_le_mul_right _ (by decide)
  generalize (liftKeyInd1Stage tlSigDdhKeyInd S (sigKeyInd1KeyProg S b.q_total)).size = sL at hLift ⊢
  generalize (sigKeyInd1KeyProg S b.q_total).size = sD at hLift hSz
  generalize red1LitSize (sigKeyInd1KeyProg S b.q_total) = sR at hLift hLit
  generalize _root_.ReductionDsl.reductionSizeBudget = sB at h0 ⊢
  generalize _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) = sBits at hSz h1 ⊢
  omega

theorem shcrKeyInd1KeyAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (shcrKeyInd1KeyAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hLift := liftKeyInd2Stage_size_le tlPrimKeyInd tlPrimKeyInd_sizeLe S (shcrKeyInd1KeyDslProg S b)
  have hSz := shcrKeyInd1KeyDslProg_size_le_stepCostBudget S b
  dsimp only [shcrKeyInd1KeyAtomicProg, shcrKeyInd1KeyDslProg] at hLift hSz ⊢
  have hLitEq := k1_shcrKeyInd1KeyProg_litSize_eq S b.q_total (keyIndLoopBound b)
  have hLit := ki_shcrKeyIndProg_litSize_le S b.q_total (keyIndLoopBound b)
  rw [hLitEq] at hLift
  have h0 : 310804 ≤ _root_.ReductionDsl.reductionSizeBudget := by decide
  have h1 : 2660 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ≤
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    Nat.mul_le_mul_right _ (by decide)
  generalize (liftKeyInd2Stage tlPrimKeyInd S (shcrKeyInd1KeyProg S b.q_total (keyIndLoopBound b))).size = sL at hLift ⊢
  generalize (shcrKeyInd1KeyProg S b.q_total (keyIndLoopBound b)).size = sD at hLift hSz
  generalize red2LitSize (shcrKeyIndProg S b.q_total (keyIndLoopBound b)) = sR at hLift hLit
  generalize _root_.ReductionDsl.reductionSizeBudget = sB at h0 ⊢
  generalize _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) = sBits at hSz h1 ⊢
  omega

theorem fgKeyInd1KeyGapDhAtomicProg_size_le_budget (S : Setup) (b : QueryBudget) :
    (fgKeyInd1KeyGapDhAtomicProg S b).size ≤
      _root_.ReductionDsl.reductionSizeBudget +
        2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) := by
  have hLift := liftKeyInd1Stage_size_le tlSigDdhKeyInd tlSigDdhKeyInd_sizeLe S
    (fgKeyInd1KeyGapDhDslProg S b)
  have hSz := fgKeyInd1KeyGapDh2Prog_size_le_stepCostBudget S b
  dsimp only [fgKeyInd1KeyGapDhAtomicProg, fgKeyInd1KeyGapDhDslProg] at hLift ⊢
  have hLit := k1_fgKeyInd1KeyGapDh2Prog_litSize_le S b.q_total
  have h0 : 515402 ≤ _root_.ReductionDsl.reductionSizeBudget := by decide
  have h1 : 2800 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) ≤
      2 ^ 12 * _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) :=
    Nat.mul_le_mul_right _ (by decide)
  generalize (liftKeyInd1Stage tlSigDdhKeyInd S (fgKeyInd1KeyGapDh2Prog S b.q_total)).size = sL at hLift ⊢
  generalize (fgKeyInd1KeyGapDh2Prog S b.q_total).size = sD at hLift hSz
  generalize red1LitSize (fgKeyInd1KeyGapDh2Prog S b.q_total) = sR at hLift hLit
  generalize _root_.ReductionDsl.reductionSizeBudget = sB at h0 ⊢
  generalize _root_.ReductionDsl.bits (_root_.SignalPqxdh.Security.stepCostBudget S b) = sBits at hSz h1 ⊢
  omega

theorem sigKeyInd1KeyAtomicProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ (sigKeyInd1KeyAtomicProg S b) :=
  gredBlockBounded_of_cost one_le_pqSigAndDdhIface_qCost S b ℓ
    (sigKeyInd1KeyAtomicProg S b) rfl
    (sigKeyInd1KeyAtomicProg_totalCost_le_stepCostBudget S b)
    (sigKeyInd1KeyAtomicProg_size_le_budget S b)

theorem shcrKeyInd1KeyAtomicProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRed2BlockBounded S b ℓ (shcrKeyInd1KeyAtomicProg S b) :=
  gred2BlockBounded_of_cost one_le_pqPrimIface_qCost S b ℓ
    (shcrKeyInd1KeyAtomicProg S b) rfl
    (shcrKeyInd1KeyAtomicProg_totalCost_le_stepCostBudget S b)
    (shcrKeyInd1KeyAtomicProg_size_le_budget S b)

theorem fgKeyInd1KeyGapDhAtomicProg_blocks (S : Setup) (b : QueryBudget) (ℓ : Nat) :
    GRedBlockBounded S b ℓ (fgKeyInd1KeyGapDhAtomicProg S b) :=
  gredBlockBounded_of_cost one_le_pqSigAndDdhIface_qCost S b ℓ
    (fgKeyInd1KeyGapDhAtomicProg S b) rfl
    (fgKeyInd1KeyGapDhAtomicProg_totalCost_le_stepCostBudget S b)
    (fgKeyInd1KeyGapDhAtomicProg_size_le_budget S b)

theorem sigKeyInd1KeyAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (pk : Bytes) :
    (sigKeyInd1KeyAtomicProg S b).eval adv pk = (sigKeyInd1KeyDslProg S b).eval adv pk := by
  have h := liftKeyInd1Stage_eval tlSigDdhKeyInd S (sigKeyInd1KeyDslProg S b)
    (sigKeyInd1KeyProg_init_unsupported S b.q_total)
    (sigKeyInd1KeyProg_handle_unsupported S b.q_total)
    (sigKeyInd1KeyProg_finish_unsupported S b.q_total) adv pk
  have hId : embedVal (.prod (SignalPqxdh.LegacyCosted.B 1569) (SignalPqxdh.LegacyCosted.B 64)) =
      id := by
    funext ⟨x, y⟩; rfl
  rw [hId, id_map] at h
  exact h

theorem fgKeyInd1KeyGapDhAtomicProg_eval_eq (S : Setup) (b : QueryBudget)
    (adv : Unit → OracleComp (unifSpec + keyIndSpec S) Bool) (U V : Bytes) :
    (fgKeyInd1KeyGapDhAtomicProg S b).eval adv (U, V) =
      (fgKeyInd1KeyGapDhDslProg S b).eval adv (U, V) := by
  have h := liftKeyInd1Stage_eval tlSigDdhKeyInd S (fgKeyInd1KeyGapDhDslProg S b)
    (fgKeyInd1KeyGapDh2Prog_init_unsupported S b.q_total)
    (fgKeyInd1KeyGapDh2Prog_handle_unsupported S b.q_total)
    (fgKeyInd1KeyGapDh2Prog_finish_unsupported S b.q_total) adv (U, V)
  have hId : embedVal (SignalPqxdh.LegacyCosted.B 32) = id := rfl
  rw [hId, id_map] at h
  exact h

/-- Evaluated atomic `GapSigEufCmaAdv` matching `(KeyIndCostedReductionFamily.eval R).sig b A`. -/
def sigKeyInd1KeyAtomicAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapSigEufCmaAdv where
  run pk := (sigKeyInd1KeyAtomicProg S b).eval (fun _ => A.1.run) pk
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_ddh := gdhQueryBudget S b
  q_prim := gdhPrimQueryBudget S b

/-- Evaluated atomic `KemShCrAdv` matching `(KeyIndCostedReductionFamily.eval R).shcr b A`. -/
def shcrKeyInd1KeyAtomicAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv where
  State := Mid (keyIndSpec S) Bool (shcrKeyInd1KeyAtomicProg S b).π.denote
    (shcrKeyInd1KeyAtomicProg S b).σ.denote (PB 1568).denote
  choosePk pk sk :=
    (shcrKeyInd1KeyAtomicProg S b).eval1 (fun _ => A.1.run) (pk, sk) b.q_total false
  findCollision st ss ct :=
    (shcrKeyInd1KeyAtomicProg S b).eval2 st (ss, ct) b.q_total false
  q_prim := primQueryBudget S b

/-- Evaluated atomic `GapDhWithSignAdv` matching `(KeyIndCostedReductionFamily.eval R).gdh b A`. -/
def fgKeyInd1KeyGapDhAtomicAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := (fgKeyInd1KeyGapDhAtomicProg S b).eval (fun _ => A.1.run) (U, V)
  q_ddh := gdhQueryBudget S b
  q_sig := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

theorem sigKeyInd1KeyAtomicAdv_eq_dsl (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    sigKeyInd1KeyAtomicAdv S b A = sigKeyInd1KeyDslAdv S b A :=
  congrArg
    (fun r => GapSigEufCmaAdv.mk r (2 * min S.N_spk_tot S.N_recv)
      (gdhQueryBudget S b) (gdhPrimQueryBudget S b))
    (funext fun pk => sigKeyInd1KeyAtomicProg_eval_eq S b (fun _ => A.1.run) pk)

theorem fgKeyInd1KeyGapDhAtomicAdv_eq_dsl (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    fgKeyInd1KeyGapDhAtomicAdv S b A = fgKeyInd1KeyGapDhDslAdv S b A :=
  congrArg
    (fun r => GapDhWithSignAdv.mk r (gdhQueryBudget S b)
      (2 * min S.N_spk_tot S.N_recv) (gdhPrimQueryBudget S b))
    (funext fun U => funext fun V => fgKeyInd1KeyGapDhAtomicProg_eval_eq S b (fun _ => A.1.run) U V)

theorem sigKeyInd1KeyAtomicAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (sigKeyInd1KeyAtomicAdv S b A).Bounded := by
  rw [sigKeyInd1KeyAtomicAdv_eq_dsl]
  exact sigKeyInd1KeyDslAdv_bounded S b A

theorem shcrKeyInd1KeyAtomicAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (shcrKeyInd1KeyAtomicAdv S b A).Bounded := by
  refine kemShCrAdv_bounded_of_state_retract (A := shcrKeyInd1KeyDslAdv S b A) rfl
    (embedMid (π := (shcrKeyInd1KeyDslProg S b).π) (σ := (shcrKeyInd1KeyDslProg S b).σ)
      (ch := SignalPqxdh.LegacyCosted.B 1568))
    (projMid (π := (shcrKeyInd1KeyDslProg S b).π) (σ := (shcrKeyInd1KeyDslProg S b).σ)
      (ch := SignalPqxdh.LegacyCosted.B 1568))
    (fun pk sk => ?_) (fun st' ss ct => ?_) (shcrKeyInd1KeyDslAdv_bounded S b A)
  · exact liftKeyInd2Stage_eval1 tlPrimKeyInd S (shcrKeyInd1KeyDslProg S b)
      (shcrKeyInd1KeyProg_init_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_handlePre_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_chDone_unsupported S b.q_total (keyIndLoopBound b))
      (fun _ => A.1.run) (pk, sk) b.q_total false
  · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
    have hRet := embedMid_projMid
      (π := (shcrKeyInd1KeyDslProg S b).π) (σ := (shcrKeyInd1KeyDslProg S b).σ)
      (ch := SignalPqxdh.LegacyCosted.B 1568) st'
    have h := liftKeyInd2Stage_eval2 tlPrimKeyInd S (shcrKeyInd1KeyDslProg S b)
      (shcrKeyInd1KeyProg_resume_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_handlePost_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_finish_unsupported S b.q_total (keyIndLoopBound b))
      (projMid (π := (shcrKeyInd1KeyDslProg S b).π) (σ := (shcrKeyInd1KeyDslProg S b).σ)
        (ch := SignalPqxdh.LegacyCosted.B 1568) st') (ss, ct) b.q_total false
    rw [hRet, hId, id_map] at h
    exact h

theorem fgKeyInd1KeyGapDhAtomicAdv_bounded (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    (fgKeyInd1KeyGapDhAtomicAdv S b A).Bounded := by
  rw [fgKeyInd1KeyGapDhAtomicAdv_eq_dsl]
  exact fgKeyInd1KeyGapDhDslAdv_bounded S b A

theorem GapSigEufCma_sigKeyInd1KeyAtomicAdv (P : Primitives)
    (isValidDhTriple : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    GapSigEufCma P isValidDhTriple (sigKeyInd1KeyAtomicAdv S b A) =
      GapSigEufCma P isValidDhTriple (sigReductionKeyInd1Key S b A) := by
  rw [sigKeyInd1KeyAtomicAdv_eq_dsl]
  exact GapSigEufCma_sigKeyInd1KeyDslAdv P isValidDhTriple S b A

theorem KemShCr_shcrKeyInd1KeyAtomicAdv (P : Primitives) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) :
    KemShCr P (shcrKeyInd1KeyAtomicAdv S b A) = KemShCr P (shcrReductionKeyInd1Key S b A) := by
  refine Eq.trans (kemShCr_eq_of_state_map P (shcrKeyInd1KeyDslAdv S b A)
    (shcrKeyInd1KeyAtomicAdv S b A)
    (embedMid (π := (shcrKeyInd1KeyDslProg S b).π) (σ := (shcrKeyInd1KeyDslProg S b).σ)
      (ch := SignalPqxdh.LegacyCosted.B 1568))
    (fun pk sk => ?_) (fun st ss ct => ?_))
    (KemShCr_shcrKeyInd1KeyDslAdv P S b A)
  · exact liftKeyInd2Stage_eval1 tlPrimKeyInd S (shcrKeyInd1KeyDslProg S b)
      (shcrKeyInd1KeyProg_init_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_handlePre_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_chDone_unsupported S b.q_total (keyIndLoopBound b))
      (fun _ => A.1.run) (pk, sk) b.q_total false
  · have hId : embedVal (SignalPqxdh.LegacyCosted.B 1568) = id := rfl
    have h := liftKeyInd2Stage_eval2 tlPrimKeyInd S (shcrKeyInd1KeyDslProg S b)
      (shcrKeyInd1KeyProg_resume_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_handlePost_unsupported S b.q_total (keyIndLoopBound b))
      (shcrKeyInd1KeyProg_finish_unsupported S b.q_total (keyIndLoopBound b))
      st (ss, ct) b.q_total false
    rw [hId, id_map] at h
    exact h

theorem keyIndAdvG3_1Key_le_gapDhWithSignδ_atomic
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (δ : ℝ) (hδ : KemDeltaCorrectReal P δ)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    Proofs.SignalPqxdh.Security.keyIndAdvG3_1Key S P A.1 ≤
      2 * (((S.N_spk_tot : ℝ) * ((S.N_id : ℝ) + (S.N_send_tot : ℝ)) +
            (S.N_id : ℝ) * (S.N_send_tot : ℝ) +
            (S.N_opk_tot : ℝ) * (S.N_send_opk_tot : ℝ)) *
            GapDhWithSignReal P P.isValidDhTriple P.pow8 (fgKeyInd1KeyGapDhAtomicAdv S b A)) +
      kemDecapsFailureTermReal S δ := by
  rw [fgKeyInd1KeyGapDhAtomicAdv_eq_dsl]
  exact keyIndAdvG3_1Key_le_gapDhWithSignδ_dsl S P hP δ hδ b A

end Proofs.SignalPqxdh.Security.PqxdhDelta
