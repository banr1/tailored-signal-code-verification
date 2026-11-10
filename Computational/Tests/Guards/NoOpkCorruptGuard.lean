/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Game.ModelIface
public import Computational.Specifications.Game.StatementPq

/-!
# Responder Identity-Key Corruption Guard for Promoted No-OPK Sessions

**Checked by Lean.** Because `startDR` reveals the responder's signed pre-key, corrupting that
responder's identity key in a promoted no-OPK session would violate `allTestedSessionsFresh` and
void the composed game run. Both headline `KeyInd` handlers (`bhDrvKeyInd` for `cliIface` and
`bhE2EDrvImplWith` for `modelIface`) therefore refuse `.corruptIK u` via `bhNoOpkRespPromoted`
whenever `u` is the responder of a promoted no-OPK instance. This module checks that both handlers
return `.noneResp` without modifying state when blocked, and that `bhNoOpkRespPromoted` does not
block principals without a matching promoted no-OPK instance.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Guards.NoOpkCorrupt

open OracleSpec OracleComp
open CryptoGames CryptoGames.LibsignalSM Ratchet LibsignalInst LibsignalSession
  CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalSession

variable {S : SignalPqxdh.Setup}

theorem blocked_of_noOpk (u : Fin S.N_id) (ims : List (ModelDriverInstanceMeta S)) :
    bhNoOpkRespPromoted ({ respPrin := some u, instOpkId? := none } :: ims) u = true := by
  simp [bhNoOpkRespPromoted]

theorem not_blocked_nil (u : Fin S.N_id) :
    bhNoOpkRespPromoted ([] : List (ModelDriverInstanceMeta S)) u = false :=
  rfl

theorem not_blocked_of_opk (u : Fin S.N_id) (im : ModelDriverInstanceMeta S) (opk : UInt32)
    (h : im.instOpkId? = some opk) (ims : List (ModelDriverInstanceMeta S)) :
    bhNoOpkRespPromoted (im :: ims) u = bhNoOpkRespPromoted ims u := by
  simp [bhNoOpkRespPromoted, h]

theorem not_blocked_of_other_resp (u v : Fin S.N_id) (huv : v ≠ u) (im : ModelDriverInstanceMeta S)
    (h : im.respPrin = some v) (ims : List (ModelDriverInstanceMeta S)) :
    bhNoOpkRespPromoted (im :: ims) u = bhNoOpkRespPromoted ims u := by
  simp [bhNoOpkRespPromoted, h, huv]

theorem bhDrvKeyInd_corruptIK_refused {ℓ : ℕ} (P : SignalPqxdh.Primitives) (useRo : Bool)
    (u : Fin S.N_id) (ds : ModelDriverState S ℓ) (st : SignalPqxdh.KeyIndState S)
    (h : bhNoOpkRespPromoted ds.instMeta u = true) :
    ((bhDrvKeyInd S ℓ P useRo (.corruptIK u)).run ds).run st =
      (pure ((.noneResp, ds), st) : ProbComp _) := by
  simp [bhDrvKeyInd, h]

theorem bhE2EDrvImplWith_corruptIK_refused {ℓ : ℕ} {Pt : Type} (P : SignalPqxdh.Primitives)
    (ki : QueryImpl (SignalPqxdh.keyIndSpec S) (StateT (SignalPqxdh.KeyIndState S) ProbComp))
    (C : Crypto) (K : LibsignalSpqrV1.MlKem) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (u : Fin S.N_id) (σ : BHE2EDrvState S ℓ) (h : bhNoOpkRespPromoted σ.instMeta u = true) :
    (bhE2EDrvImplWith P ki C K qep decT encT (.inr (.inl (.inl (.corruptIK u))))).run σ =
      (pure (.noneResp, σ) : ProbComp _) := by
  simp [bhE2EDrvImplWith, bhDrvKiQueryOk, h]

end CryptoVerification.E2E.Guards.NoOpkCorrupt
