/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SessionCostedFig8.Bundles

/-!
# Evaluation, `CoinSimEquiv`, and `QuerySubsumes` Bridges for Atomic `Fig8CostedReds`

Proves evaluation, `CoinSimEquiv`, `HooksVRInv (RSReach maxForwardJumps)`, and `QuerySubsumes`
bridges for the guarded atomic Figure 8 compilers and `Bundles.fig8RedsInst`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

open OracleSpec OracleComp
open _root_.ReductionDsl (CostedReduction fig8SmIface fig8SmIfaceDF fig8SmCodec fig8SmCodecDF
  ckaTargetIface prngTargetIface fsaeadHeaderIface)
open Computational.Proofs.ReductionDsl.MacroLift (toVal guardRed_pos)
open Computational.Proofs.ReductionDsl.PureAuxMacroLift (CoinSimEquiv
  compilePureAuxRed_eval compilePureAuxRed_coinSimEquiv)
open Computational.Proofs.ReductionDsl.Fig8Atomic (dhSchemeFb aeadAtomic fsAtomic fsAtomicB)
open Computational.Proofs.SessionCostedFig8.QuerySubsumes (QuerySubsumes)
open Computational.Proofs.SessionCostedFig8.Bundles (fSortSM toDenSM fSortCKA toDenCKA
  fig8SmOpsShallow fig8CkaOpsShallow
  fig8SplitIn_eval fig8AdaptQ_eval_sm fig8AdaptR_eval_sm
  fig8AdaptQDF_eval_sm fig8AdaptRDF_eval_sm
  fig8AdaptQ_eval_cka fig8AdaptR_eval_cka
  fig8AdaptQDF_eval_cka fig8AdaptRDF_eval_cka
  smPureAuxBundle smDFPureAuxBundle ckaPureAuxBundle prngPureAuxBundle fsPureAuxBundle
  smToFig8Adapters smDFToFig8Adapters ckaToFig8Adapters ckaDFToFig8Adapters
  smOpMacro_eval smPureAuxBundle_samp_eval smDFPureAuxBundle_samp_eval
  smPureAuxBundle_query_eval smDFPureAuxBundle_query_eval
  ckaOpMacro_eval ckaPureAuxBundle_samp_coinSimEquiv ckaPureAuxBundle_query_eval
  prngPureAuxBundle_samp_coinSimEquiv prngPureAuxBundle_query_eval
  fsPureAuxBundle_samp_coinSimEquiv fsPureAuxBundle_query_eval fsPureAuxBundle_samp_querySubsumes
  compileSmAtomic compileSmDFAtomic compileCkaAtomic compileCkaDFAtomic
  compilePrngAtomic compilePrngDFAtomic compileFsAtomic compileFsDFAtomic
  fig8RedsInst challSimDFAtomicProg redCKAAuthDFAtomicProg redPRNGAuthDFAtomicProg
  redFSAuthDFAtomicProg)
open CryptoGames (Party FSAEADScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun ckaIface ckaSMCodec ckaSMCodecDF)
open CryptoGames.PRFPRNG (prngIface prngSMCodec prngSMCodecDF fsaeadHeaderAdIface)
open CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState fromAEADPRG)
open CryptoGames.Ratchet (rootPRNG)
open CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32
  lPubOf lChainPRG)
open CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey SignalMessageProtoCodec
  maxForwardJumps)
open CryptoGames.LibsignalSM (lBlank)
open CryptoGames.SM (smIface smIfaceDF smCodec smCodecDF MakesAtMostQueries
  challSimProg challSimProg_eval privRedBProg privRedBProg_eval challSimDFProg)
open CryptoGames.SM.Engine (RSReach HooksVRInv)
open CryptoGames.SM.Construction (Header Mode SchemeAdversary fsClamp
  hooksCKA hooksCKA_startRecv_rs hooksCKA_commit_vR
  hooksPRNG hooksPRNG_startRecv_rs hooksPRNG_commit_vR
  redCKAAuth redCKAAuthProg redCKAAuthProg_eval_vr
  redCKAPriv redCKAPrivProg redCKAPrivProg_eval_vr
  redPRNGAuth redPRNGAuthProg redPRNGAuthProg_branch_eval_vr redPRNGAuthProg_advantage_vr
  redPRNGPriv redPRNGPrivProg redPRNGPrivProg_branch_eval_vr redPRNGPrivProg_advantage_vr
  redFSAuth redFSAuthProg redFSAuthProg_eval_clamp
  redFSPriv redFSPrivProg redFSPrivProg_eval_clamp
  redFSPrivCoin redFSPrivCoinProg redFSPrivCoinProg_eval_clamp)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

namespace Computational.Proofs.SessionCostedFig8.BundlesEval

/-! ## Generic atomic compiler bridges -/

section CompilerEval

variable (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
  (C : Crypto) (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
  (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)

theorem compileSmAtomic_eval (hℓ : ℓ < 10 ^ 6)
    (R : CostedReduction (fig8SmOpsShallow ℓ Pt)
      (smIface Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (smCodec Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    (compileSmAtomic ℓ Pt C Dh encPt encT idOf lam R).eval (fun _ => A) () =
      R.eval (fun _ => A) () := by
  unfold compileSmAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_eval
    (smPureAuxBundle ℓ Pt C Dh encPt encT lam)
    (smToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenSM ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (smOpMacro_eval ℓ Pt C Dh encPt encT idOf lam)
    (smPureAuxBundle_samp_eval ℓ Pt C Dh encPt encT idOf lam)
    (smPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam)
    (fig8AdaptQ_eval_sm ℓ Pt C Dh encPt encT lam)
    (fig8AdaptR_eval_sm ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compileSmDFAtomic_eval (hℓ : ℓ < 10 ^ 6)
    (R : CostedReduction (fig8SmOpsShallow ℓ Pt)
      (smIfaceDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (smCodecDF Unit (Fig8St Pt) Unit (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) Unit (Fig8C Pt))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    (compileSmDFAtomic ℓ Pt C Dh encPt encT idOf lam R).eval (fun _ => A) () =
      R.eval (fun _ => A) () := by
  unfold compileSmDFAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_eval
    (smDFPureAuxBundle ℓ Pt C Dh encPt encT lam)
    (smDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenSM ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (smOpMacro_eval ℓ Pt C Dh encPt encT idOf lam)
    (smDFPureAuxBundle_samp_eval ℓ Pt C Dh encPt encT idOf lam)
    (smDFPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam)
    (fig8AdaptQDF_eval_sm ℓ Pt C Dh encPt encT lam)
    (fig8AdaptRDF_eval_sm ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compileCkaAtomic_coinSimEquiv (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ckaSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      ((compileCkaAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compileCkaAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_coinSimEquiv
    (ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (ckaPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (ckaPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compileCkaDFAtomic_coinSimEquiv (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (ckaSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      ((compileCkaDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compileCkaDFAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_coinSimEquiv
    (ckaPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (ckaPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (ckaPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fig8AdaptQDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptRDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compilePrngAtomic_coinSimEquiv (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      ((compilePrngAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compilePrngAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_coinSimEquiv
    (prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (prngPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (prngPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compilePrngDFAtomic_coinSimEquiv (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      ((compilePrngDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compilePrngDFAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_coinSimEquiv
    (prngPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (prngPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (prngPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fig8AdaptQDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptRDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compileFsAtomic_coinSimEquiv (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      ((compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compileFsAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_coinSimEquiv
    (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (fsPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compileFsDFAtomic_coinSimEquiv (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compileFsDFAtomic
  rw [guardRed_pos hℓ]
  have h := compilePureAuxRed_coinSimEquiv
    (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (fun _ => rfl)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsPureAuxBundle_samp_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (fsPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fig8AdaptQDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptRDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compileFsAtomic_querySubsumes (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    QuerySubsumes
      ((compileFsAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compileFsAtomic
  rw [guardRed_pos hℓ]
  have h := QuerySubsumes.compilePureAuxRed_querySubsumes
    (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (fsPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fun _ => rfl) (fun _ => rfl)
    (fig8AdaptQ_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptR_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

theorem compileFsDFAtomic_querySubsumes (hℓ : ℓ < 10 ^ 6) (B0 : ℕ)
    (R : CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
        (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.specDF (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodecDF (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool)
    (A : OracleComp (unifSpec + CryptoGames.SM.specDF (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool) :
    QuerySubsumes
      ((compileFsDFAtomic ℓ Pt C Dh encPt encT idOf lam B0 R).eval (fun _ => A) ())
      (R.eval (fun _ => A) ()) := by
  unfold compileFsDFAtomic
  rw [guardRed_pos hℓ]
  have h := QuerySubsumes.compilePureAuxRed_querySubsumes
    (fsPureAuxBundle ℓ Pt C Dh encPt encT idOf lam B0 ($ᵗ (BitVec 256)))
    (ckaDFToFig8Adapters ℓ Pt C Dh encPt encT idOf lam)
    R (toDenCKA ℓ Pt) () () (idOf .A, idOf .B)
    (fig8SplitIn_eval ℓ Pt C Dh encPt encT idOf lam)
    (ckaOpMacro_eval ℓ Pt C Dh encPt encT idOf lam B0)
    (fsPureAuxBundle_samp_querySubsumes ℓ Pt C Dh encPt encT idOf lam B0)
    (fun g z => .of_eq (fsPureAuxBundle_query_eval ℓ Pt C Dh encPt encT idOf lam B0 _ g z))
    (fun _ => rfl) (fun _ => rfl)
    (fig8AdaptQDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fig8AdaptRDF_eval_cka ℓ Pt C Dh encPt encT lam)
    (fun _ => A) (fun _ => A) id
    (fun _ => .of_eq (id_map A).symm)
    (fun _ => rfl)
    (outEq := id) (fun _ => rfl)
  rwa [id_map] at h

end CompilerEval

/-! ## `RSReach` invariant and shallow evaluation bridges -/

section ShallowEval

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

theorem rsReach_take {CK MK : Type} {maxSkip k : ℕ} (B0 : ℕ)
    {v : RatchetReceiverState CK MK} (hv : RSReach maxSkip k v) :
    RSReach maxSkip k { v with skippedKeys := v.skippedKeys.take B0 } :=
  ⟨hv.1, fun kv hkv => hv.2 kv (List.mem_of_mem_take hkv)⟩

omit [DecidableEq Pt] [Zero Pt] [SampleableType Pt] in
theorem fsAtomicB_receive_rsReach (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (B0 k : ℕ)
    {v v' : RatchetReceiverState (BitVec 256) (BitVec 256)}
    {a : Header Pt} {c : ℕ × LibsignalCiphertextWithSalt32}
    {i : ℕ} {m : LibsignalMsgPublicPart × Plain ℓ}
    (hv : RSReach maxForwardJumps k v)
    (hrec : (fsAtomicB C ℓ encT idOf B0).receive v a c = some (v', i, m)) :
    i ≤ (k + 1) * (maxForwardJumps + 1) ∧ RSReach maxForwardJumps (k + 1) v' :=
  RSReach.receive
    ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
    (lChainPRG C.F) maxForwardJumps k (rsReach_take B0 hv) hrec

omit [Zero Pt] [SampleableType Pt] in
theorem hooksCKA_vrInv_fsAtomicB (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 Δcka : ℕ) (mo : Mode) :
    HooksVRInv (RSReach maxForwardJumps)
      (hooksCKA (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) Δcka mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σ Tn h :=
    hooksCKA_startRecv_rs (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
      Δcka mo
      (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps)
      ctx P t γ σ Tn h
  fsRecv_step _ _ _ rs hdr e _ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksCKA] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨hrec, _⟩
    exact (fsAtomicB_receive_rsReach C ℓ encT idOf B0 _ hVR hrec.symm).2
  commit_vR :=
    hooksCKA_commit_vR (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) Δcka mo

omit [Zero Pt] [SampleableType Pt] in
theorem hooksPRNG_vrInv_fsAtomicB (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (B0 : ℕ) (mo : Mode) :
    HooksVRInv (RSReach maxForwardJumps)
      (hooksPRNG (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) mo) where
  mono hle hv := hv.mono hle
  startRecv_step ctx P t γ σv Tn h :=
    hooksPRNG_startRecv_rs (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) mo
      (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
        (lChainPRG C.F) maxForwardJumps)
      ctx P t γ σv Tn h
  fsRecv_step _ _ _ rs hdr e _ h res hVR hmem v' i' m' hEq := by
    rcases res with ⟨ans, h'⟩
    dsimp only at hEq
    subst hEq
    dsimp only [hooksPRNG] at hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, Option.some.injEq] at hmem
    rcases hmem with ⟨hrec, _⟩
    exact (fsAtomicB_receive_rsReach C ℓ encT idOf B0 _ hVR hrec.symm).2
  commit_vR :=
    hooksPRNG_commit_vR (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0) mo

omit [Zero Pt] in
theorem redCKAAuthProg_eval_atomic (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((redCKAAuthProg (q + 1) B0 1 qep maxForwardJumps tL t :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    redCKAAuth (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
      lam 1 qep tL t A := by
  intro B0
  exact redCKAAuthProg_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksCKA_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 1 ⟨true, tL, t⟩)
    (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redCKAPrivProg_eval_atomic (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((redCKAPrivProg (q + 1) B0 1 qep maxForwardJumps tL i :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (ckaIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
          (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    redCKAPriv (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
      lam 1 qep tL i A := by
  intro B0
  exact redCKAPrivProg_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksCKA_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 1 ⟨false, tL, i⟩)
    (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redPRNGAuthProg_branch_eval_atomic (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) (b_prng : Bool) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b_prng
      ((redPRNGAuthProg (q + 1) B0 1 qep maxForwardJumps tL t :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b_prng
      (redPRNGAuth (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
        lam 1 qep tL t A) := by
  intro B0
  exact redPRNGAuthProg_branch_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksPRNG_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 ⟨true, tL, t⟩)
    (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q) b_prng

omit [Zero Pt] in
theorem redPRNGAuthProg_advantage_atomic (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      ((redPRNGAuthProg (q + 1) B0 1 qep maxForwardJumps tL t :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (redPRNGAuth (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
        lam 1 qep tL t A) := by
  intro B0
  exact redPRNGAuthProg_advantage_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksPRNG_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 ⟨true, tL, t⟩)
    (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redPRNGPrivProg_branch_eval_atomic (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) (b_prng : Bool) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b_prng
      ((redPRNGPrivProg (q + 1) B0 1 qep maxForwardJumps tL i :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.branch (rootPRNG C.F encPt) b_prng
      (redPRNGPriv (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
        lam 1 qep tL i A) := by
  intro B0
  exact redPRNGPrivProg_branch_eval_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksPRNG_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 ⟨false, tL, i⟩)
    (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q) b_prng

omit [Zero Pt] in
theorem redPRNGPrivProg_advantage_atomic (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      ((redPRNGPrivProg (q + 1) B0 1 qep maxForwardJumps tL i :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    CryptoGames.PRFPRNG.advantage (rootPRNG C.F encPt)
      (redPRNGPriv (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
        lam 1 qep tL i A) := by
  intro B0
  exact redPRNGPrivProg_advantage_vr
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (hooksPRNG_vrInv_fsAtomicB Dh encPt C ℓ encT idOf B0 ⟨false, tL, i⟩)
    (RSReach.init ((aeadAtomic C ℓ encT idOf).movePubPartToAD (lPubOf protoSignalCodec))
      (lChainPRG C.F) maxForwardJumps)
    (fun _ _ _ _ _ _ hVR hrec =>
      (fsAtomicB_receive_rsReach C ℓ encT idOf B0 q hVR hrec).1)
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redFSAuthProg_eval_atomic_clamp (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((redFSAuthProg (q + 1) B0 1 qep maxForwardJumps j tL t :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    redFSAuth (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
      lam 1 qep j tL t A := by
  intro B0
  exact redFSAuthProg_eval_clamp
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep j tL t
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redFSPrivProg_eval_atomic_clamp (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((redFSPrivProg (q + 1) B0 1 qep maxForwardJumps tL i :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    redFSPriv (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
      lam 1 qep tL i A := by
  intro B0
  exact redFSPrivProg_eval_clamp
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

omit [Zero Pt] in
theorem redFSPrivCoinProg_eval_atomic_clamp (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt)
    (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    ((redFSPrivCoinProg (q + 1) B0 1 qep maxForwardJumps tL i :
      CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
        (fsaeadHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
          (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
          (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
          (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
          ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
        _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) =
    redFSPrivCoin (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
      lam 1 qep tL i A := by
  intro B0
  exact redFSPrivCoinProg_eval_clamp
    (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsAtomicB C ℓ encT idOf B0)
    (q + 1) B0 q 1 qep tL i
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.le_refl _) (Nat.mul_le_mul (Nat.le_succ q) (Nat.le_succ q))
    A q hqA (Nat.le_refl q)

end ShallowEval

/-! ## `Bundles.fig8RedsInst` bridges -/

section ConcreteInstEval

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

local instance : Inhabited Pt := ⟨0⟩

theorem fig8RedsInst_challSim_eval (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hqA : MakesAtMostQueries A q) :
    ((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).challSim.eval (fun _ => A) ()) =
      CryptoGames.SM.Thm1.challSim (2 + 1) qep A := by
  dsimp only [fig8RedsInst]
  rw [compileSmAtomic_eval ℓ Pt C Dh encPt encT idOf lam hℓ]
  refine challSimProg_eval q (2 + 1) qep rfl _ q ?_ (Nat.le_refl q)
  exact hqA

theorem fig8RedsInst_privRedB_eval (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6)
    (encT : Pt → PublicKey) (idOf : Party → IdentityKey) (lam : Pt) (qep q i : ℕ)
    (A : OracleComp (unifSpec + CryptoGames.SM.spec (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) Bool)
    (hqA : MakesAtMostQueries A q) :
    (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).privRedB i).eval (fun _ => A) ()) =
      CryptoGames.SM.ThmB.privRedB (2 + 1) qep i (lBlank ℓ) A := by
  dsimp only [fig8RedsInst]
  rw [compileSmAtomic_eval ℓ Pt C Dh encPt encT idOf lam hℓ]
  refine privRedBProg_eval q (2 + 1) qep i rfl _ q ?_ (Nat.le_refl q)
  exact hqA

theorem fig8RedsInst_redCKAAuth_coinSimEquiv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAAuth tL t).eval
        (fun _ => A) ())
      (redCKAAuth (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf ((q + 1) * (maxForwardJumps + 1))) lam 1 qep tL t A) := by
  dsimp only [fig8RedsInst]
  rw [← redCKAAuthProg_eval_atomic Dh encPt C ℓ encT idOf lam qep q tL t A hqA]
  exact compileCkaAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ _ _ A

theorem fig8RedsInst_redCKAPriv_coinSimEquiv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    CoinSimEquiv (ckaTargetIface ℓ Pt).fwdU
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redCKAPriv tL i).eval
        (fun _ => A) ())
      (redCKAPriv (dhSchemeFb Dh) (rootPRNG C.F encPt)
        (fsAtomicB C ℓ encT idOf ((q + 1) * (maxForwardJumps + 1))) lam 1 qep tL i A) := by
  dsimp only [fig8RedsInst]
  rw [← redCKAPrivProg_eval_atomic Dh encPt C ℓ encT idOf lam qep q tL i A hqA]
  exact compileCkaAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ _ _ A

theorem fig8RedsInst_redPRNGAuth_prog_coinSimEquiv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32)) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGAuth tL t).eval
        (fun _ => A) ())
      ((redPRNGAuthProg (q + 1) B0 1 qep maxForwardJumps tL t :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) := by
  intro B0
  dsimp only [fig8RedsInst]
  exact compilePrngAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem fig8RedsInst_redPRNGPriv_prog_coinSimEquiv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32)) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (prngTargetIface ℓ Pt).fwdU
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redPRNGPriv tL i).eval
        (fun _ => A) ())
      ((redPRNGPrivProg (q + 1) B0 1 qep maxForwardJumps tL i :
        CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
          (prngIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt) (BitVec 256) Pt Pt
            (BitVec 256) (BitVec 256) (BitVec 256)
            (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
            (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
            ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
          _ _ .unit .unit .bool .bool).eval (fun _ => A) ()) := by
  intro B0
  dsimp only [fig8RedsInst]
  exact compilePrngAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A


theorem fig8RedsInst_redFSAuth_coinSimEquiv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSAuth j tL t).eval
        (fun _ => A) ())
      (redFSAuth (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam 1 qep j tL t A) := by
  intro B0
  dsimp only [fig8RedsInst]
  rw [← redFSAuthProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam qep q j tL t A hqA]
  exact compileFsAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem fig8RedsInst_redFSPriv_coinSimEquiv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv tL i).eval
        (fun _ => A) ())
      (redFSPriv (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam 1 qep tL i A) := by
  intro B0
  dsimp only [fig8RedsInst]
  rw [← redFSPrivProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam qep q tL i A hqA]
  exact compileFsAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem fig8RedsInst_redFSPrivCoin_coinSimEquiv (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    CoinSimEquiv (fsaeadHeaderIface ℓ Pt).fwdU
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin tL i).eval
        (fun _ => A) ())
      (redFSPrivCoin (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam 1 qep tL i A) := by
  intro B0
  dsimp only [fig8RedsInst]
  rw [← redFSPrivCoinProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam qep q tL i A hqA]
  exact compileFsAtomic_coinSimEquiv ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem fig8RedsInst_redFSAuth_querySubsumes (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (j : ℕ) (tL : Option ℕ) (t : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    QuerySubsumes
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSAuth j tL t).eval
        (fun _ => A) ())
      (redFSAuth (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam 1 qep j tL t A) := by
  intro B0
  dsimp only [fig8RedsInst]
  rw [← redFSAuthProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam qep q j tL t A hqA]
  exact compileFsAtomic_querySubsumes ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem fig8RedsInst_redFSPriv_querySubsumes (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    QuerySubsumes
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPriv tL i).eval
        (fun _ => A) ())
      (redFSPriv (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam 1 qep tL i A) := by
  intro B0
  dsimp only [fig8RedsInst]
  rw [← redFSPrivProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam qep q tL i A hqA]
  exact compileFsAtomic_querySubsumes ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

theorem fig8RedsInst_redFSPrivCoin_querySubsumes (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (C : Crypto) (codec : SignalMessageProtoCodec)
    (ℓ : ℕ) (hℓ : ℓ < 10 ^ 6) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (lam : Pt) (qep q : ℕ) (tL : Option ℕ) (i : ℕ)
    (A : SchemeAdversary (CryptoGames.CKA.DDH.State (BitVec 256) Pt) Pt (BitVec 256)
      (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (ℕ × LibsignalCiphertextWithSalt32))
    (hqA : MakesAtMostQueries A q) :
    let B0 := (q + 1) * (maxForwardJumps + 1)
    QuerySubsumes
      (((fig8RedsInst Dh encPt C codec ℓ encT idOf lam qep q).redFSPrivCoin tL i).eval
        (fun _ => A) ())
      (redFSPrivCoin (dhSchemeFb Dh) (rootPRNG C.F encPt) (fsClamp B0 (fsAtomicB C ℓ encT idOf B0))
        lam 1 qep tL i A) := by
  intro B0
  dsimp only [fig8RedsInst]
  rw [← redFSPrivCoinProg_eval_atomic_clamp Dh encPt C ℓ encT idOf lam qep q tL i A hqA]
  exact compileFsAtomic_querySubsumes ℓ Pt C Dh encPt encT idOf lam hℓ B0 _ A

end ConcreteInstEval

end Computational.Proofs.SessionCostedFig8.BundlesEval
