/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.AtomicLift -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCr -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfCk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyAeadCpa -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase -- proof-setup: allow-public-import

/-!
# Two-Fuel Handshake Arms, Shadow Handles, and Kind-Split `Auth` Programs

Assembles two-fuel `(K_on, K_ro)` handshake and PRF branches with AVL-shadowed query handlers over
`pqAtomicOps`. Packages the kind-split one-key `Auth` reductions (`shcrAuth1KeyKindProg`,
`prfCk1KeyKindProg`, `prfMsgKeys1KeyKindProg`, `aeadCpa1KeyKindProg`, and `prfHmac1KeyKindProg`).
-/

public section

set_option autoImplicit false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms

open _root_.ReductionDsl
  (Ty Var Env Expr Comp Iface CostedReduction TwoStageCostedReduction
   pqAtomicSig pqAtomicOps PB)
open _root_.Computational.Proofs.SignalPqxdh.AtomicLift
  (embedTy mapExpr mapComp exprRename compRename tlAuthPrim tlPrfMk tlPrfHmac
   aiAuthPrim aiPrfMk aiPrfHmac)
open _root_.SignalPqxdh (Setup QueryBudget authSpec)
open _root_.SignalPqxdh.Costed (authCodec pqAuthPrimIface pqPrfMkIface pqPrfHmacIface)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (shcrStTy pauseTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (authHybridStateFixedTy prfCkStTy prfMkStTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (cpaStTy cpaPayloadTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac (hmStTy)
open Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK
  (AuthKindFuels roBothAvlTy emptyRoBothAvlE authBaseShadowStTy authFixedShadowStTy
   baseRoCacheE baseRootRoCacheE fixedRoCacheE fixedRootRoCacheE
   authQueryAtomicTy authSendQAtomicTy authRecvQAtomicTy authRespAtomicTy
   dispatchAuthQ initPrin1KeyFuelB initPrin1KeyKB corruptKB genOpkKB genSpkKB registerKB
   initPrin1KeyFixedKB corruptFixedKB genSpkFixedKB genOpkFixedKB registerFixedKB
   finalizeAuthFixedKDsl aNoneAtomicE roBaseShadowArmC roRootBaseShadowArmC
   roFixedShadowArmC roRootFixedShadowArmC syncRoBothC syncBaseShadowRespC syncFixedShadowRespC)

section HsBranches

open _root_.SignalPqxdh.Security.ReductionDsl (principalEntryTy spkBundleEntryTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (Ext sendQTy recvQTy RS SCS FinTy)

@[expose] def sendKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  AuthCoreKArmsHs.sendKC S K_on K_ro opk st x

@[expose] def recvTailKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  AuthCoreKArmsHs.recvTailKC S K_on K_ro opk st x kE bE oSk?

@[expose] def recvKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  AuthCoreKArmsHs.recvKB S K_on K_ro opk st x

@[expose] def shcrFinishSendKC (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ FinTy :=
  AuthCoreKArmsHs.shcrFinishSendKC K_on K_ro st d ks sc

@[expose] def shcrSendKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  AuthCoreKArmsHs.shcrSendKC S K_on K_ro opk s x

@[expose] def shcrAcceptKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  AuthCoreKArmsHs.shcrAcceptKB S K_on K_ro opk s x

@[expose] def shcrResumeKC (K_on1 K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  AuthCoreKArmsHs.shcrResumeKC K_on1 K_ro sc d s

end HsBranches

section PrfBranches

open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (Ext sendQTy recvQTy RSF prfMkCoreTy prfMkStepPreTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (cpaSlotSendResTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
  (muStTy intPrepTy schedPrepArgsTy schedPrepTy schedArgsTy schedResTy hmRecvDataTy hmResTy hmPreTy)

@[expose] def authCkSendKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  AuthCoreKArmsBase.authCkSendKB S K_on K_ro opk idx chalP fhst x

@[expose] def authCkRecvKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  AuthCoreKArmsBase.authCkRecvKB S K_on K_ro opk idx chalP fhst x

@[expose] def authMkSendPreKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  AuthCoreKArmsBase.authMkSendPreKB S K_on K_ro opk core x

@[expose] def authMkRecvPreKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  AuthCoreKArmsBase.authMkRecvPreKB S K_on K_ro opk core x

@[expose] def cpaSendSlotKB (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ cpaSlotSendResTy :=
  AuthCoreKArmsBase.cpaSendSlotKB S K_on K_ro opk allowPause idx ns fhst x

@[expose] def cpaRecvKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  AuthCoreKArmsBase.cpaRecvKC S K_on K_ro opk fhst x

@[expose] def intSendPrepKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt intPrepTy) :=
  AuthCoreKArmsBase.intSendPrepKC S K_on K_ro opk fhst x

@[expose] def hmSendKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  AuthCoreKArmsBase.hmSendKC S K_on K_ro opk jt fhst mst x

@[expose] def hmSchedPrepKC (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) : Comp pqxdhOps pqPrimIface Δ (.opt schedPrepTy) :=
  AuthCoreKArmsBase.hmSchedPrepKC S K_on K_ro a

@[expose] def hmSchedKC (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedArgsTy) : Comp pqxdhOps pqPrimIface Δ schedResTy :=
  AuthCoreKArmsBase.hmSchedKC S K_on K_ro a

@[expose] def hmRecvTailKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    Comp pqxdhOps pqPrimIface Δ hmResTy :=
  AuthCoreKArmsBase.hmRecvTailKC S K_on K_ro opk jt fhst mst x d

@[expose] def hmRecvKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  AuthCoreKArmsBase.hmRecvKC S K_on K_ro opk jt fhst mst x

end PrfBranches

@[expose] def dropShadow0 {a : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig} :
    Var [a] t → Var (a :: Γ) t
  | .zero => .zero

@[expose] def dropShadow1 {s : Ty pqAtomicSig} {Γ : List (Ty pqAtomicSig)} {t : Ty pqAtomicSig} :
    Var (s :: Γ) t → Var (s :: .prod s roBothAvlTy :: Γ) t
  | .zero => .zero
  | .succ v => .succ (.succ v)

@[expose] def liftAuthPrim1 {a r : Ty pqSig} (c : Comp pqxdhOps pqPrimIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) :
    Comp pqAtomicOps pqAuthPrimIface Γ (embedTy r) :=
  .bind (.ret e) (compRename dropShadow0 (mapComp tlAuthPrim c))

@[expose] def syncShcrShadowRespC (cap : ℕ) {Γ : List (Ty pqAtomicSig)}
    (scsE : Expr pqAtomicOps Γ (.prod authRespAtomicTy (embedTy shcrStTy)))
    (roBothE : Expr pqAtomicOps Γ roBothAvlTy) :
    Comp pqAtomicOps pqAuthPrimIface Γ
      (.prod authRespAtomicTy (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  .bind (.ret (.pair scsE roBothE))
    (.bind (syncRoBothC cap
        (baseRoCacheE (.fst (.snd (.fst .v0))))
        (baseRootRoCacheE (.fst (.snd (.fst .v0))))
        (.snd .v0))
      (.ret (.pair (.fst (.fst .v1)) (.pair (.snd (.fst .v1)) .v0))))

@[expose] def shcrBaseArmC (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.Ext Γ₂ Δ],
      Var Γ₁ authStateTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.RS)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface
      (embedTy arg :: .prod (embedTy shcrStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  .bind (liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun st =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
       step st x)
      (.pair (.fst (.fst .v1)) .v0))
    (.ret (.pair (.fst .v0) (.pair (.pair (.snd .v0) (.snd (.fst .v2))) (.snd .v2))))

@[expose] def shcrKindInitC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface [.prod (PB 1568) (PB 3168)]
      (.prod .unit (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  .bind (mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S F.K_on F.K_on).init)
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) emptyRoBothAvlE)))

@[expose] def shcrKindHandlePostC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  let sendArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [authSendQAtomicTy, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy)) :=
    .bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         shcrSendKC S F.K_on F.K_ro opk s x)
        (.pair (.fst .v1) .v0))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2))
  let recvArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [authRecvQAtomicTy, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy)) :=
    .bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         shcrAcceptKB S F.K_on F.K_ro opk s x)
        (.pair (.fst .v1) .v0))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2))
  dispatchAuthQ (.var (.succ .zero))
    (shcrBaseArmC (S := S) (fun st u => initPrin1KeyKB F st u))
    (shcrBaseArmC (S := S) (fun st u => corruptKB F st u))
    (.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S F.K_on s x)
        (.pair (.fst .v1) .v0))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2)))))
    (shcrBaseArmC (S := S) (fun st x => genOpkKB F st x))
    (sendArm true)
    (sendArm false)
    (recvArm true)
    (recvArm false)
    (.bind (roBaseShadowArmC aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0)
        (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0))))))
    (.bind (roRootBaseShadowArmC aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0)
        (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0))))))
    (.ret (.pair aNoneAtomicE .v1))
    (shcrBaseArmC (S := S) (fun st sk => registerKB st sk))

@[expose] def shcrKindHandlePreC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
      (.sum (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))
        (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy)))) :=
  let wrapInl {a : Ty pqAtomicSig}
      (m : Comp pqAtomicOps pqAuthPrimIface
        [a, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))) :=
    Comp.bind m (.ret (.inl .v0))
  let sendPreArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [authSendQAtomicTy, .prod (embedTy shcrStTy) roBothAvlTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy))
          (.prod (PB 1568) (.prod (embedTy pauseTy) (.prod (embedTy shcrStTy) roBothAvlTy)))) :=
    .bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.bindV
           (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.tryPauseC S F.K_on opk s x) fun p =>
         .ret (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.eCaseOpt
           (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v p) .noneE fun d =>
           .someE (.pair (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.buPqspkB
             (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.pdBu
               (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d)))
             (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.v d))))
        (.pair (.fst .v1) .v0))
      (.caseOpt .v0
        (.bind (.bind (liftAuthPrim1
            (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
             _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
             shcrSendKC S F.K_on F.K_ro opk s x)
            (.pair (.fst .v2) .v1))
          (syncShcrShadowRespC F.K_cap .v0 (.snd .v3)))
          (.ret (.inl .v0)))
        (.ret (.inr (.pair (.fst .v0) (.pair (.snd .v0) .v3)))))
  dispatchAuthQ (.var (.succ .zero))
    (wrapInl (shcrBaseArmC (S := S) (fun st u => initPrin1KeyKB F st u)))
    (wrapInl (shcrBaseArmC (S := S) (fun st u => corruptKB F st u)))
    (wrapInl (.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrGenSpkB S F.K_on s x)
        (.pair (.fst .v1) .v0))
      (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v2))))))
    (wrapInl (shcrBaseArmC (S := S) (fun st x => genOpkKB F st x)))
    (sendPreArm true)
    (sendPreArm false)
    (wrapInl (.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         shcrAcceptKB S F.K_on F.K_ro true s x)
        (.pair (.fst .v1) .v0))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2))))
    (wrapInl (.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.var (.succ .zero))) fun x =>
         shcrAcceptKB S F.K_on F.K_ro false s x)
        (.pair (.fst .v1) .v0))
      (syncShcrShadowRespC F.K_cap .v0 (.snd .v2))))
    (wrapInl (.bind (roBaseShadowArmC aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0)
        (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0)))))))
    (wrapInl (.bind (roRootBaseShadowArmC aiAuthPrim F.K_cap (.pair (.fst (.fst .v1)) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0)
        (.pair (.pair (.fst (.snd .v0)) (.snd (.fst .v2))) (.snd (.snd .v0)))))))
    (.ret (.inl (.pair aNoneAtomicE .v1)))
    (wrapInl (shcrBaseArmC (S := S) (fun st sk => registerKB st sk)))

@[expose] def shcrKindChDoneC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface [.prod (embedTy shcrStTy) roBothAvlTy, .bool] (PB 1568) :=
  .bind (.ret (.fst .v0))
    (compRename dropShadow1
      (mapComp tlAuthPrim
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S F.K_on F.K_on).chDone))

@[expose] def shcrKindResumeC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy shcrStTy) roBothAvlTy, embedTy pauseTy, .prod (PB 32) (PB 1568)]
      (.prod (authCodec S).R (.prod (embedTy shcrStTy) roBothAvlTy)) :=
  .bind (liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.var .zero)) fun s =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.fst (.snd (.var (.succ .zero)))) fun d =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthHs.letV (.snd (.snd (.var (.succ (.succ .zero))))) fun sc =>
       shcrResumeKC F.K_on1 F.K_ro sc d s)
      (.pair (.fst .v0) (.pair .v1 .v2)))
    (syncShcrShadowRespC F.K_cap .v0 (.snd .v1))

@[expose] def shcrKindFinishC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy shcrStTy) roBothAvlTy, .bool, .prod (PB 32) (PB 1568)] (PB 1568) :=
  .bind (.ret (.fst .v0))
    (compRename dropShadow1
      (mapComp tlAuthPrim
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthHs.shcrReductionAuthProg S F.K_on F.K_on).finish))

@[expose] def prfCkKindInitC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqAuthPrimIface [.prod (PB 32) (PB 32)]
      (.prod .unit (.prod (embedTy prfCkStTy) roBothAvlTy)) :=
  .bind (mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkInitDslK S b.q_total))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) emptyRoBothAvlE)))

@[expose] def ckRebuildE {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy prfCkStTy))
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) :
    Expr pqAtomicOps Γ (.prod (embedTy prfCkStTy) roBothAvlTy) :=
  .pair (.pair (.fst sE) (.pair (.fst (.snd sE)) (.pair (.fst (.snd (.snd sE))) (.fst fsE))))
    (.snd fsE)

@[expose] def ckBaseArmC (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface
      (embedTy arg :: .prod (embedTy prfCkStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy)) :=
  .bind (liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       step fhst x)
      (.pair (.snd (.snd (.snd (.fst .v1)))) .v0))
    (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.pair (.snd .v0) (.snd .v2)))))

@[expose] def prfCkKindHandleC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy)) :=
  let sendArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [authSendQAtomicTy, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy)) :=
    .bind (.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV
           (.fst (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun idx =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV
           (.fst (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)))) fun chalP =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV
           (.snd (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)))) fun fhst =>
         authCkSendKB S F.K_on F.K_ro opk idx chalP fhst x)
        (.pair (.fst .v1) .v0))
      (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0))))
  let recvArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [authRecvQAtomicTy, .prod (embedTy prfCkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfCkStTy) roBothAvlTy)) :=
    .bind (.bind (liftAuthPrim1
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun s =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV
           (.fst (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s))) fun idx =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV
           (.fst (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)))) fun chalP =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV
           (.snd (.snd (.snd (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.v s)))) fun fhst =>
         authCkRecvKB S F.K_on F.K_ro opk idx chalP fhst x)
        (.pair (.fst .v1) .v0))
      (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
      (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0))))
  dispatchAuthQ (.var (.succ .zero))
    (ckBaseArmC S (fun fhst u => initPrin1KeyFixedKB F fhst u))
    (ckBaseArmC S (fun fhst u => corruptFixedKB F fhst u))
    (ckBaseArmC S (fun fhst x => genSpkFixedKB F fhst x))
    (ckBaseArmC S (fun fhst x => genOpkFixedKB F fhst x))
    (sendArm true)
    (sendArm false)
    (recvArm true)
    (recvArm false)
    (.bind (roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.snd (.fst .v1)))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0)))))
    (.bind (roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.snd (.fst .v1)))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (ckRebuildE (.fst .v2) (.snd .v0)))))
    (.ret (.pair aNoneAtomicE .v1))
    (ckBaseArmC S (fun fhst sk => registerFixedKB fhst sk))

@[expose] def prfCkKindFinishC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface [.prod (embedTy prfCkStTy) roBothAvlTy, .bool] .bool :=
  .bind (.ret (.fst .v0))
    (compRename dropShadow1
      (mapComp tlAuthPrim
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfCkFinishDsl S F.K_on)))

@[expose] def prfMkKindInitC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqPrfMkIface [.unit]
      (.prod .unit (.prod (embedTy prfMkStTy) roBothAvlTy)) :=
  .bind (mapComp tlPrfMk
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMsgKeysInitDslK S b.q_total))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) emptyRoBothAvlE)))

@[expose] def liftPrfMk1 {a r : Ty pqSig}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) :
    Comp pqAtomicOps pqPrfMkIface Γ (embedTy r) :=
  .bind (.ret e) (compRename dropShadow0 (mapComp tlPrfMk c))

@[expose] def mkRebuildE {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy prfMkStTy))
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) :
    Expr pqAtomicOps Γ (.prod (embedTy prfMkStTy) roBothAvlTy) :=
  .pair (.pair (.fst sE) (.pair (.fst (.snd sE))
    (.pair (.fst (.snd (.snd sE))) (.pair (.fst (.snd (.snd (.snd sE)))) (.fst fsE)))))
    (.snd fsE)

@[expose] def mkBaseArmC (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqPrfMkIface
      (embedTy arg :: .prod (embedTy prfMkStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy)) :=
  .bind (liftPrfMk1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
         step fhst x))
      (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) .v0))
    (.ret (.pair (.fst .v0) (mkRebuildE (.fst .v2) (.pair (.snd .v0) (.snd .v2)))))

section PrfHandles

open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf
  (v letV bindV caseSumV natEq aNone queryDeriveMk liftPrimComp prfMkStepPostC)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac (queryHmacEval hmContX0E hmPostC)

@[expose] def mkPostRunC (S : Setup) (K_on : ℕ) {Δ : List (Ty pqSig)}
    (bud : Var Δ .nat) (core : Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkCoreTy)
    (pre : Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkStepPreTy) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfMkIface Δ
      (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy prfMkStTy) :=
  caseSumV (v pre)
    (fun d => .ret (.pair (.fst (v d)) (.pair (v bud) (.snd (v d)))))
    fun req =>
      .ite (natEq (v bud) (.nat 0))
        (.ret (.pair aNone (.pair (.nat 0) (v core))))
        (letV (.fst (v req)) fun salt? =>
         letV (.snd (v req)) fun cont =>
         bindV (queryDeriveMk (v salt?)) fun mk =>
         bindV (liftPrimComp (prfMkStepPostC S K_on cont mk)) fun post =>
         .ret (.pair (.fst (v post))
           (.pair (.sub (v bud) (.nat 1)) (.snd (v post)))))

@[expose] def prfMkKindHandleC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqPrfMkIface
      [.prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy)) :=
  let onlineArm {arg : Ty pqSig}
      (preStep : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)}
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
        Var Γ₁ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkCoreTy → Var Γ₂ arg →
        Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMkStepPreTy) :
      Comp pqAtomicOps pqPrfMkIface
        [embedTy arg, .prod (embedTy prfMkStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy prfMkStTy) roBothAvlTy)) :=
    .bind (liftPrfMk1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun _bud =>
         letV (.snd (v s)) fun core =>
         bindV (liftPrimComp (preStep core x)) fun _pre =>
         mkPostRunC S F.K_on (.succ (.succ .zero)) (.succ .zero) .zero)
        (.pair (.fst .v1) .v0))
      (.bind (syncRoBothC F.K_cap
          (fixedRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
          (fixedRootRoCacheE (.snd (.snd (.snd (.snd (.snd .v0))))))
          (.snd .v2))
        (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
  dispatchAuthQ (.var (.succ .zero))
    (mkBaseArmC S (fun fhst u => initPrin1KeyFixedKB F fhst u))
    (mkBaseArmC S (fun fhst u => corruptFixedKB F fhst u))
    (mkBaseArmC S (fun fhst x => genSpkFixedKB F fhst x))
    (mkBaseArmC S (fun fhst x => genOpkFixedKB F fhst x))
    (onlineArm (fun core x => authMkSendPreKB S F.K_on F.K_ro true core x))
    (onlineArm (fun core x => authMkSendPreKB S F.K_on F.K_ro false core x))
    (onlineArm (fun core x => authMkRecvPreKB S F.K_on F.K_ro true core x))
    (onlineArm (fun core x => authMkRecvPreKB S F.K_on F.K_ro false core x))
    (.bind (roFixedShadowArmC aiPrfMk F.K_cap
        (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (mkRebuildE (.fst .v2) (.snd .v0)))))
    (.bind (roRootFixedShadowArmC aiPrfMk F.K_cap
        (.pair (.snd (.snd (.snd (.snd (.fst .v1))))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (mkRebuildE (.fst .v2) (.snd .v0)))))
    (.ret (.pair aNoneAtomicE .v1))
    (mkBaseArmC S (fun fhst sk => registerFixedKB fhst sk))

@[expose] def prfMkKindFinishC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqPrfMkIface [.prod (embedTy prfMkStTy) roBothAvlTy, .bool] .bool :=
  .bind (.ret (.fst .v0))
    (compRename dropShadow1
      (mapComp tlPrfMk
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.prfMsgKeysFinishDsl S F.K_on)))

@[expose] def cpaKindInitC (S : Setup) (b : QueryBudget) :
    Comp pqAtomicOps pqAuthPrimIface [.unit]
      (.prod .unit (.prod (embedTy cpaStTy) roBothAvlTy)) :=
  .bind (mapComp tlAuthPrim
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaInitC S b.q_total))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) emptyRoBothAvlE)))

@[expose] def cpaRebuildE {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy cpaStTy))
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) :
    Expr pqAtomicOps Γ (.prod (embedTy cpaStTy) roBothAvlTy) :=
  .pair (.pair (.fst sE) (.pair (.fst (.snd sE)) (.fst fsE))) (.snd fsE)

@[expose] def cpaBaseArmC (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface
      (embedTy arg :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) :=
  .bind (liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       step fhst x)
      (.pair (.snd (.snd (.fst .v1))) .v0))
    (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.pair (.snd .v0) (.snd .v2)))))

@[expose] def cpaRecvArmC (S : Setup) (F : AuthKindFuels) (opk : Bool) {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqAuthPrimIface
      (authRecvQAtomicTy :: .prod (embedTy cpaStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) :=
  .bind (.bind (liftAuthPrim1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
       _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
       cpaRecvKC S F.K_on F.K_ro opk fhst x)
      (.pair (.snd (.snd (.fst .v1))) .v0))
    (syncFixedShadowRespC F.K_cap .v0 (.snd .v2)))
    (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0))))

@[expose] def cpaKindHandlePreC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
      (.sum (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))
        (.prod (.prod (PB 158) (.prod (PB 32) (PB 32)))
          (.prod (embedTy cpaPayloadTy) (.prod (embedTy cpaStTy) roBothAvlTy)))) :=
  let wrapInl {a : Ty pqAtomicSig}
      (m : Comp pqAtomicOps pqAuthPrimIface
        [a, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))) :=
    Comp.bind m (.ret (.inl .v0))
  let sendPreArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.sum (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy))
          (.prod (.prod (PB 158) (.prod (PB 32) (PB 32)))
            (.prod (embedTy cpaPayloadTy) (.prod (embedTy cpaStTy) roBothAvlTy)))) :=
    .bind (liftAuthPrim1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun idx =>
         letV (.fst (.snd (v s))) fun ns =>
         letV (.snd (.snd (v s))) fun fhst =>
         bindV (cpaSendSlotKB S F.K_on F.K_ro opk true idx ns fhst x) fun r =>
         caseSumV (v r)
           (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
           (fun p => .ret (.inr (.pair (.fst (v p))
             (.pair (.fst (.snd (v p))) (.pair (v idx) (.snd (.snd (v p)))))))))
        (.pair (.fst .v1) .v0))
      (.caseSum .v0
        (.bind (syncRoBothC F.K_cap
            (fixedRoCacheE (.snd (.snd (.snd .v0))))
            (fixedRootRoCacheE (.snd (.snd (.snd .v0))))
            (.snd .v3))
          (.ret (.inl (.pair (.fst .v1) (.pair (.snd .v1) .v0)))))
        (.ret (.inr (.pair (.fst .v0)
          (.pair (.fst (.snd .v0)) (.pair (.snd (.snd .v0)) (.snd .v3)))))))
  dispatchAuthQ (.var (.succ .zero))
    (wrapInl (cpaBaseArmC S (fun fhst u => initPrin1KeyFixedKB F fhst u)))
    (wrapInl (cpaBaseArmC S (fun fhst u => corruptFixedKB F fhst u)))
    (wrapInl (cpaBaseArmC S (fun fhst x => genSpkFixedKB F fhst x)))
    (wrapInl (cpaBaseArmC S (fun fhst x => genOpkFixedKB F fhst x)))
    (sendPreArm true)
    (sendPreArm false)
    (wrapInl (cpaRecvArmC S F true))
    (wrapInl (cpaRecvArmC S F false))
    (wrapInl (.bind (roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0))))))
    (wrapInl (.bind (roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0))))))
    (.ret (.inl (.pair aNoneAtomicE .v1)))
    (wrapInl (cpaBaseArmC S (fun fhst sk => registerFixedKB fhst sk)))

@[expose] def cpaKindChDoneC :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy cpaStTy) roBothAvlTy, .bool]
      (.prod (PB 158) (.prod (PB 32) (PB 32))) :=
  .bind (.ret (.fst .v0))
    (compRename dropShadow1
      (mapComp tlAuthPrim _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaDefaultChC))

@[expose] def cpaKindResumeC (S : Setup) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy cpaStTy) roBothAvlTy, embedTy cpaPayloadTy, .opt (PB 32)]
      (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) :=
  .bind (.bind (.ret (.fst .v0))
      (compRename dropShadow1
        (mapComp tlAuthPrim _root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaResumeC)))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) (.snd .v1))))

@[expose] def cpaKindHandlePostC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) :=
  let sendPostArm (opk : Bool) :
      Comp pqAtomicOps pqAuthPrimIface
        [authSendQAtomicTy, .prod (embedTy cpaStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy cpaStTy) roBothAvlTy)) :=
    .bind (liftAuthPrim1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun idx =>
         letV (.fst (.snd (v s))) fun ns =>
         letV (.snd (.snd (v s))) fun fhst =>
         bindV (cpaSendSlotKB S F.K_on F.K_ro opk false idx ns fhst x) fun r =>
         caseSumV (v r)
           (fun d => .ret (.pair (.fst (v d)) (.pair (v idx) (.snd (v d)))))
           (fun _ => .ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst))))))
        (.pair (.fst .v1) .v0))
      (.bind (syncRoBothC F.K_cap
          (fixedRoCacheE (.snd (.snd (.snd .v0))))
          (fixedRootRoCacheE (.snd (.snd (.snd .v0))))
          (.snd .v2))
        (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
  dispatchAuthQ (.var (.succ .zero))
    (cpaBaseArmC S (fun fhst u => initPrin1KeyFixedKB F fhst u))
    (cpaBaseArmC S (fun fhst u => corruptFixedKB F fhst u))
    (cpaBaseArmC S (fun fhst x => genSpkFixedKB F fhst x))
    (cpaBaseArmC S (fun fhst x => genOpkFixedKB F fhst x))
    (sendPostArm true)
    (sendPostArm false)
    (cpaRecvArmC S F true)
    (cpaRecvArmC S F false)
    (.bind (roFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))))
    (.bind (roRootFixedShadowArmC aiAuthPrim F.K_cap (.pair (.snd (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (cpaRebuildE (.fst .v2) (.snd .v0)))))
    (.ret (.pair aNoneAtomicE .v1))
    (cpaBaseArmC S (fun fhst sk => registerFixedKB fhst sk))

@[expose] def cpaKindFinishC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqAuthPrimIface
      [.prod (embedTy cpaStTy) roBothAvlTy, .bool, .opt (PB 32)] .bool :=
  .bind (.ret (.fst .v0))
    (compRename dropShadow1
      (mapComp tlAuthPrim
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthAead.cpaFinishC S F.K_on)))

@[expose] def prfHmacKindInitC (S : Setup) :
    Comp pqAtomicOps pqPrfHmacIface [.unit]
      (.prod .unit (.prod (embedTy hmStTy) roBothAvlTy)) :=
  .bind (mapComp tlPrfHmac
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmInitC S))
    (.ret (.pair (.fst .v0) (.pair (.snd .v0) emptyRoBothAvlE)))

@[expose] def liftPrfHmac1 {a r : Ty pqSig}
    (c : Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface [a] r)
    {Γ : List (Ty pqAtomicSig)} (e : Expr pqAtomicOps Γ (embedTy a)) :
    Comp pqAtomicOps pqPrfHmacIface Γ (embedTy r) :=
  .bind (.ret e) (compRename dropShadow0 (mapComp tlPrfHmac c))

@[expose] def hmRebuildE {Γ : List (Ty pqAtomicSig)}
    (sE : Expr pqAtomicOps Γ (embedTy hmStTy))
    (fsE : Expr pqAtomicOps Γ authFixedShadowStTy) :
    Expr pqAtomicOps Γ (.prod (embedTy hmStTy) roBothAvlTy) :=
  .pair (.pair (.fst sE) (.pair (.fst fsE) (.snd (.snd sE)))) (.snd fsE)

@[expose] def hmBaseArmC (S : Setup) {arg : Ty pqSig}
    (step : ∀ {Γ₁ Γ₂ Δ : List (Ty pqSig)} [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
      [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ],
      Var Γ₁ authHybridStateFixedTy → Var Γ₂ arg →
      Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.RSF)
    {Γ : List (Ty pqAtomicSig)} :
    Comp pqAtomicOps pqPrfHmacIface
      (embedTy arg :: .prod (embedTy hmStTy) roBothAvlTy :: Γ)
      (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy)) :=
  .bind (liftPrfHmac1
      (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.liftPrimComp
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.fst (.var .zero)) fun fhst =>
         _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.letV (.snd (.var (.succ .zero))) fun x =>
         step fhst x))
      (.pair (.fst (.snd (.fst .v1))) .v0))
    (.ret (.pair (.fst .v0) (hmRebuildE (.fst .v2) (.pair (.snd .v0) (.snd .v2)))))

@[expose] def hmPostRunC (K_on : ℕ) {Δ : List (Ty pqSig)}
    (jt : Var Δ .nat) (pre : Var Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPreTy) :
    Comp pqxdhOps _root_.SignalPqxdh.LegacyCosted.pqPrfHmacIface Δ
      (.prod _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.authRespTy hmStTy) :=
  caseSumV (v pre)
    (fun r => .ret (.pair (.fst (.fst (v r)))
      (.pair (v jt) (.pair (.snd (.fst (v r))) (.snd (v r))))))
    fun c =>
      bindV (queryHmacEval (hmContX0E (v c))) fun t =>
      bindV (liftPrimComp (hmPostC K_on (.pair (v c) (v t)))) fun r =>
      .ret (.pair (.fst (.fst (v r)))
        (.pair (v jt) (.pair (.snd (.fst (v r))) (.snd (v r)))))

@[expose] def prfHmacKindHandleC (S : Setup) (F : AuthKindFuels) :
    Comp pqAtomicOps pqPrfHmacIface
      [.prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
      (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy)) :=
  let onlineArm {arg : Ty pqSig}
      (preStep : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₁ Δ]
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₂ Δ]
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₃ Δ]
        [_root_.SignalPqxdh.Security.ReductionDsl.AuthPrf.Ext Γ₄ Δ],
        Var Γ₁ .nat → Var Γ₂ authHybridStateFixedTy →
        Var Γ₃ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.muStTy → Var Γ₄ arg →
        Comp pqxdhOps pqPrimIface Δ _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmPreTy) :
      Comp pqAtomicOps pqPrfHmacIface
        [embedTy arg, .prod (embedTy hmStTy) roBothAvlTy, (authCodec S).Q]
        (.prod (authCodec S).R (.prod (embedTy hmStTy) roBothAvlTy)) :=
    .bind (liftPrfHmac1
        (letV (.fst (.var .zero)) fun s =>
         letV (.snd (.var (.succ .zero))) fun x =>
         letV (.fst (v s)) fun jt =>
         letV (.fst (.snd (v s))) fun fhst =>
         letV (.snd (.snd (v s))) fun mst =>
         bindV (liftPrimComp (preStep jt fhst mst x)) fun _pre =>
         hmPostRunC F.K_on (.succ (.succ (.succ .zero))) .zero)
        (.pair (.fst .v1) .v0))
      (.bind (syncRoBothC F.K_cap
          (fixedRoCacheE (.fst (.snd (.snd .v0))))
          (fixedRootRoCacheE (.fst (.snd (.snd .v0))))
          (.snd .v2))
        (.ret (.pair (.fst .v1) (.pair (.snd .v1) .v0))))
  dispatchAuthQ (.var (.succ .zero))
    (hmBaseArmC S (fun fhst u => initPrin1KeyFixedKB F fhst u))
    (hmBaseArmC S (fun fhst u => corruptFixedKB F fhst u))
    (hmBaseArmC S (fun fhst x => genSpkFixedKB F fhst x))
    (hmBaseArmC S (fun fhst x => genOpkFixedKB F fhst x))
    (onlineArm (fun jt fhst mst x => hmSendKC S F.K_on F.K_ro true jt fhst mst x))
    (onlineArm (fun jt fhst mst x => hmSendKC S F.K_on F.K_ro false jt fhst mst x))
    (onlineArm (fun jt fhst mst x => hmRecvKC S F.K_on F.K_ro true jt fhst mst x))
    (onlineArm (fun jt fhst mst x => hmRecvKC S F.K_on F.K_ro false jt fhst mst x))
    (.bind (roFixedShadowArmC aiPrfHmac F.K_cap (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (hmRebuildE (.fst .v2) (.snd .v0)))))
    (.bind (roRootFixedShadowArmC aiPrfHmac F.K_cap (.pair (.fst (.snd (.fst .v1))) (.snd .v1)) .v0)
      (.ret (.pair (.fst .v0) (hmRebuildE (.fst .v2) (.snd .v0)))))
    (.ret (.pair aNoneAtomicE .v1))
    (hmBaseArmC S (fun fhst sk => registerFixedKB fhst sk))

@[expose] def prfHmacKindFinishC (F : AuthKindFuels) :
    Comp pqAtomicOps pqPrfHmacIface [.prod (embedTy hmStTy) roBothAvlTy, .bool] .bool :=
  .bind (.ret (.fst .v0))
    (compRename dropShadow1
      (mapComp tlPrfHmac
        (_root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac.hmFinishC F.K_on)))

end PrfHandles

@[expose] def shcrAuth1KeyKindProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 1568) (PB 3168)) .unit .bool (PB 1568)
      (.prod (PB 32) (PB 1568)) (PB 1568) :=
  let F := AuthKindFuels.ofBudget S b
  { σ := .prod (embedTy shcrStTy) roBothAvlTy
    π := embedTy pauseTy
    init := shcrKindInitC S F
    handlePre := shcrKindHandlePreC S F
    chDone := shcrKindChDoneC S F
    resume := shcrKindResumeC S F
    handlePost := shcrKindHandlePostC S F
    finish := shcrKindFinishC S F }

@[expose] def prfCk1KeyKindProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      (.prod (PB 32) (PB 32)) .unit .bool .bool :=
  let F := AuthKindFuels.ofBudget S b
  { σ := .prod (embedTy prfCkStTy) roBothAvlTy
    init := prfCkKindInitC S b
    handle := prfCkKindHandleC S F
    finish := prfCkKindFinishC S F }

@[expose] def prfMsgKeys1KeyKindProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfMkIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  let F := AuthKindFuels.ofBudget S b
  { σ := .prod (embedTy prfMkStTy) roBothAvlTy
    init := prfMkKindInitC S b
    handle := prfMkKindHandleC S F
    finish := prfMkKindFinishC S F }

@[expose] def aeadCpa1KeyKindProg (S : Setup) (b : QueryBudget) :
    TwoStageCostedReduction pqAtomicOps pqAuthPrimIface (authSpec S) (authCodec S)
      .unit .unit .bool (.prod (PB 158) (.prod (PB 32) (PB 32)))
      (.opt (PB 32)) .bool :=
  let F := AuthKindFuels.ofBudget S b
  { σ := .prod (embedTy cpaStTy) roBothAvlTy
    π := embedTy cpaPayloadTy
    init := cpaKindInitC S b
    handlePre := cpaKindHandlePreC S F
    chDone := cpaKindChDoneC
    resume := cpaKindResumeC S
    handlePost := cpaKindHandlePostC S F
    finish := cpaKindFinishC S F }

@[expose] def prfHmac1KeyKindProg (S : Setup) (b : QueryBudget) :
    CostedReduction pqAtomicOps pqPrfHmacIface (authSpec S) (authCodec S)
      .unit .unit .bool .bool :=
  let F := AuthKindFuels.ofBudget S b
  { σ := .prod (embedTy hmStTy) roBothAvlTy
    init := prfHmacKindInitC S
    handle := prfHmacKindHandleC S F
    finish := prfHmacKindFinishC F }

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArms
