/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.Auth.Headline
public import Computational.Proofs.SignalPqxdh.Delta.Auth1KeyHeadline -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.AtomicSizeHonest
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindSigBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindGdhBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfBounds
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindSiggdhEq
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrEq
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaEq
import Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfEq

/-!
# One-Key PQXDH δ `Auth` Kind-Split Reduction Bundle

Packages the per-query-kind costed reduction family `pqxdhAuth1KeyKindCostedSims` with its
syntactic resource bounds (`Auth1KeyCostedReductionBounds`), semantic query bounds
(`Auth1KeyReductionQueryBounds`), and advantage transfer lemmas into `auth1KeyKindDslFamily`.
-/

namespace Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindBundle

public section

set_option autoImplicit false

open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.Security (Auth1KeyCostedReductionBounds Auth1KeyReductionQueryBounds)
open _root_.Computational.Proofs.ReductionDsl.AtomicSizeHonest
  (pqAtomicOps_sizeHonest pqAtomicSamplers_sizeHonest)
open _root_.Proofs.SignalPqxdh.Security.PqxdhDelta (Auth1KeyDslFamily)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindProgs
  (pqxdhAuth1KeyKindCostedSims)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindSigBounds
  (auth1KeyKindSig_totalCost_le_stepCostBudget auth1KeyKindSig_q_sig
   auth1KeyKindSig_q_ddh auth1KeyKindSig_q_prim auth1KeyKindSig_blocks
   auth1KeyKindSig_costByKind)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindGdhBounds
  (auth1KeyKindGdh_totalCost_le_stepCostBudget auth1KeyKindGdh_q_sig
   auth1KeyKindGdh_q_ddh auth1KeyKindGdh_q_prim auth1KeyKindGdh_blocks
   auth1KeyKindGdh_costByKind)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrBounds
  (shcrAuth1KeyKindProg_totalCost_le_stepCostBudget shcrAuth1KeyKindProg_q_prim
   shcrAuth1KeyKindProg_blocks shcrAuth1KeyKindProg_costByKind
   pqxdhAuth1KeyKind_shcr_bounded)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaBounds
  (aeadCpa1KeyKindProg_totalCost_le_stepCostBudget aeadCpa1KeyKindProg_q_prim
   aeadCpa1KeyKindProg_blocks aeadCpa1KeyKindProg_costByKind
   pqxdhAuth1KeyKind_cpa_bounded)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfBounds
  (prfCk1KeyKindProg_totalCost_le_stepCostBudget
   prfMsgKeys1KeyKindProg_totalCost_le_stepCostBudget
   prfHmac1KeyKindProg_totalCost_le_stepCostBudget
   prfCk1KeyKindProg_q_prim prfMsgKeys1KeyKindProg_q_prim prfHmac1KeyKindProg_q_prim
   prfCk1KeyKindProg_blocks prfMsgKeys1KeyKindProg_blocks prfHmac1KeyKindProg_blocks
   prfCk1KeyKindProg_costByKind prfMsgKeys1KeyKindProg_costByKind prfHmac1KeyKindProg_costByKind)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindSiggdhEq
  (pqxdhAuth1KeyKind_sig_bounded pqxdhAuth1KeyKind_sig_le
   pqxdhAuth1KeyKind_gdh_bounded pqxdhAuth1KeyKind_gdh_le)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindShcrEq
  (pqxdhAuth1KeyKind_shcr_le)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindCpaEq
  (pqxdhAuth1KeyKind_cpa_le)
open Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindPrfEq
  (pqxdhAuth1KeyKind_ck_bounded pqxdhAuth1KeyKind_ck_le
   pqxdhAuth1KeyKind_mk_bounded pqxdhAuth1KeyKind_mk_le
   pqxdhAuth1KeyKind_int_bounded pqxdhAuth1KeyKind_int_le)

/-- Syntactic cost, query, block-size, and per-kind cost bounds for `pqxdhAuth1KeyKindCostedSims S`. -/
theorem pqxdhAuth1KeyKindCostedSims_costedBounds (S : Setup) :
    Auth1KeyCostedReductionBounds S (pqxdhAuth1KeyKindCostedSims S) where
  ops_sizeHonest  := pqAtomicOps_sizeHonest
  samp_sizeHonest := pqAtomicSamplers_sizeHonest
  sig_cost        := auth1KeyKindSig_totalCost_le_stepCostBudget S
  shcr_cost       := shcrAuth1KeyKindProg_totalCost_le_stepCostBudget S
  gdh_cost        := auth1KeyKindGdh_totalCost_le_stepCostBudget S
  ck_cost         := prfCk1KeyKindProg_totalCost_le_stepCostBudget S
  mk_cost         := prfMsgKeys1KeyKindProg_totalCost_le_stepCostBudget S
  cpa_cost        := aeadCpa1KeyKindProg_totalCost_le_stepCostBudget S
  int_cost        := prfHmac1KeyKindProg_totalCost_le_stepCostBudget S
  sig_q_sig       := auth1KeyKindSig_q_sig S
  sig_q_ddh       := auth1KeyKindSig_q_ddh S
  sig_q_prim      := auth1KeyKindSig_q_prim S
  shcr_q_prim     := shcrAuth1KeyKindProg_q_prim S
  gdh_q_sig       := auth1KeyKindGdh_q_sig S
  gdh_q_ddh       := auth1KeyKindGdh_q_ddh S
  gdh_q_prim      := auth1KeyKindGdh_q_prim S
  ck_q_prim       := prfCk1KeyKindProg_q_prim S
  mk_q_prim       := prfMsgKeys1KeyKindProg_q_prim S
  cpa_q_prim      := aeadCpa1KeyKindProg_q_prim S
  int_q_prim      := prfHmac1KeyKindProg_q_prim S
  sig_blocks      := auth1KeyKindSig_blocks S
  shcr_blocks     := shcrAuth1KeyKindProg_blocks S
  gdh_blocks      := auth1KeyKindGdh_blocks S
  ck_blocks       := prfCk1KeyKindProg_blocks S
  mk_blocks       := prfMsgKeys1KeyKindProg_blocks S
  cpa_blocks      := aeadCpa1KeyKindProg_blocks S
  int_blocks      := prfHmac1KeyKindProg_blocks S
  sig_costByKind  := auth1KeyKindSig_costByKind S
  shcr_costByKind := shcrAuth1KeyKindProg_costByKind S
  gdh_costByKind  := auth1KeyKindGdh_costByKind S
  ck_costByKind   := prfCk1KeyKindProg_costByKind S
  mk_costByKind   := prfMsgKeys1KeyKindProg_costByKind S
  cpa_costByKind  := aeadCpa1KeyKindProg_costByKind S
  int_costByKind  := prfHmac1KeyKindProg_costByKind S

/-- Semantic query bounds for `(pqxdhAuth1KeyKindCostedSims S).eval`. -/
theorem pqxdhAuth1KeyKindCostedSims_simBounds (S : Setup) :
    Auth1KeyReductionQueryBounds S (pqxdhAuth1KeyKindCostedSims S).eval where
  sig_bounded  := pqxdhAuth1KeyKind_sig_bounded S
  shcr_bounded := pqxdhAuth1KeyKind_shcr_bounded S
  gdh_bounded  := pqxdhAuth1KeyKind_gdh_bounded S
  ck_bounded   := pqxdhAuth1KeyKind_ck_bounded S
  mk_bounded   := pqxdhAuth1KeyKind_mk_bounded S
  cpa_bounded  := pqxdhAuth1KeyKind_cpa_bounded S
  int_bounded  := pqxdhAuth1KeyKind_int_bounded S

/-- One-key `Auth` `ReductionDsl` family backed by `pqxdhAuth1KeyKindCostedSims S`. -/
def auth1KeyKindDslFamily (S : Setup) : Auth1KeyDslFamily S where
  R           := pqxdhAuth1KeyKindCostedSims S
  bounds      := pqxdhAuth1KeyKindCostedSims_costedBounds S
  queryBounds := pqxdhAuth1KeyKindCostedSims_simBounds S
  sig_le P b A  := pqxdhAuth1KeyKind_sig_le P S b A
  gdh_le P b A  := pqxdhAuth1KeyKind_gdh_le P S b A
  shcr_le P b A := pqxdhAuth1KeyKind_shcr_le P S b A
  ck_le P b A   := pqxdhAuth1KeyKind_ck_le P S b A
  mk_le P b A   := pqxdhAuth1KeyKind_mk_le P S b A
  cpa_le P b A  := pqxdhAuth1KeyKind_cpa_le P S b A
  int_le P b A  := pqxdhAuth1KeyKind_int_le P S b A

end

end Computational.Proofs.SignalPqxdh.Delta.KindSplit.Auth1KeyKindBundle
