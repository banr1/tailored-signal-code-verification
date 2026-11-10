/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpa

/-!
# `ReductionDsl` Program for the `Auth` `PrfHmac` Reduction

Defines `prfHmacRedProg`, the single-stage `ReductionDsl` witness over `pqPrfHmacIface`
for the fused `Auth` `PrfHmac` reduction (`prfHmacReductionAuth`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthPrfHmac

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf SignalPqxdh.Security.ReductionDsl.AuthAead
open OracleSpec OracleComp

/-! ## State and Continuation Types -/

/-- Multi-key identifier: `.inl sid` for initiator sessions, `.inr rc` for responder non-matched receive counts. -/
abbrev muKeyIdTy : PT := .sum sessionIdTy .nat
abbrev muKeysTy : PT := .list (.prod muKeyIdTy (.prod .nat msgKeysTy))
abbrev muChalTy : PT := .list (.prod muKeyIdTy (.prod (B 158) (B 32)))
abbrev muPendTy : PT := .list (.prod .nat (.prod (B 359) (B 32)))
/-- Multi-key reduction state `(keys, (chal, (pending, bad)))`. -/
abbrev muStTy : PT := .prod muKeysTy (.prod muChalTy (.prod muPendTy .bool))

/-- Full `prfHmacRedProg` state `(jt, (fhst, mst))`. -/
abbrev hmStTy : PT := .prod .nat (.prod authHybridStateFixedTy muStTy)

abbrev encContTy : PT := .prod muKeyIdTy (.prod .nat (.prod (B 158) (.prod (B 24) muStTy)))

abbrev encPreTy : PT := .sum (.prod (.opt (B 32)) muStTy) encContTy

abbrev intPrepTy : PT :=
  .prod principalEntryTy (.prod (.opt (.prod .nat principalEntryTy))
    (.prod (.prod .bool (.prod .bool (B 32)))
      (.prod (.prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 1568) (.prod (B 32) (B 32))))))
        (.prod drKeyTy (.prod (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))
          (.prod (.opt (B 32)) (.prod (B 32) (.prod (B 158) (.prod provTy
            (.prod (.list (.prod (B 192) drKeyTy))
              (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))))))))))))

abbrev intFinArgsTy : PT :=
  .prod authHybridStateFixedTy (.prod sessionIdTy (.prod preKeyBundleTy
    (.prod (.prod (B 32) (B 32)) (.prod intPrepTy (.prod msgKeysTy (B 32))))))

abbrev hmSendContTy : PT :=
  .prod sessionIdTy (.prod preKeyBundleTy (.prod (.prod (B 32) (B 32))
    (.prod intPrepTy (.prod authHybridStateFixedTy encContTy))))

abbrev hmResTy : PT := .prod RSF muStTy

abbrev hmPreTy : PT := .sum hmResTy hmSendContTy

abbrev hmRecvDataTy : PT :=
  .prod principalEntryTy (.prod spkBundleEntryTy (.prod (.opt (B 32)) (.prod (B 192)
    (.prod authHybridStateTy (.prod (.list (.prod .nat (.prod U32 (.prod U32 (B 32)))))
      .bool)))))

abbrev schedPrepTy : PT :=
  .prod .bool (.prod (.opt idealAuthSessionTy) (.prod .bool (.prod drKeyTy
    (.prod (.list (.prod (B 192) drKeyTy)) (.prod .bool (.prod (B 32) (.prod (B 32)
      (.prod (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))
        (.prod (B 32) (.prod (B 32) (.opt (B 32))))))))))))

abbrev schedOutTy : PT :=
  .opt (.prod drKeyTy (.prod (B 32) (.prod (B 32) (.prod (B 32)
    (.prod (.list (.prod (B 192) drKeyTy))
      (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))))))))

abbrev schedResTy : PT := .prod (.prod schedOutTy authMkSaltCacheTy) muStTy

abbrev schedFinArgsTy : PT :=
  .prod .nat (.prod principalEntryTy (.prod preKeyMsgTy (.prod .nat (.prod authMkSaltCacheTy
    (.prod schedPrepTy muStTy)))))

abbrev schedPrepArgsTy : PT :=
  .prod authHybridStateTy (.prod principalEntryTy (.prod spkBundleEntryTy (.prod (.opt (B 32))
    (.prod (B 192) preKeyMsgTy))))

abbrev schedArgsTy : PT :=
  .prod .nat (.prod .nat (.prod authMkSaltCacheTy (.prod schedPrepArgsTy muStTy)))

/-! ## Expression and Interface Helpers -/

section ExprHelpers

variable {Γ : List PT}

def bytesTake (w : ℕ+) (n : Expr pqxdhOps Γ .nat) (x : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ (B w) :=
  Expr.op (O := pqxdhOps) (Sum.inl (.take w)) (.pair n x)

def bytesDrop (w : ℕ+) (n : Expr pqxdhOps Γ .nat) (x : Expr pqxdhOps Γ (B w)) : Expr pqxdhOps Γ (B w) :=
  Expr.op (O := pqxdhOps) (Sum.inl (.drop w)) (.pair n x)

def queryHmacEval (x : Expr pqxdhOps Γ (B 359)) : Comp pqxdhOps pqPrfHmacIface Γ (B 32) :=
  Comp.query (I := pqPrfHmacIface) (Sum.inr (359 : ℕ+)) x

def natLe (a b : Expr pqxdhOps Γ .nat) : Expr pqxdhOps Γ .bool := .not (.lt b a)

def muKeys (s : Expr pqxdhOps Γ muStTy) : Expr pqxdhOps Γ muKeysTy := .fst s
def muChal (s : Expr pqxdhOps Γ muStTy) : Expr pqxdhOps Γ muChalTy := .fst (.snd s)
def muPend (s : Expr pqxdhOps Γ muStTy) : Expr pqxdhOps Γ muPendTy := .fst (.snd (.snd s))
def muBad (s : Expr pqxdhOps Γ muStTy) : Expr pqxdhOps Γ .bool := .snd (.snd (.snd s))
@[reducible] def muMk (k : Expr pqxdhOps Γ muKeysTy) (c : Expr pqxdhOps Γ muChalTy)
    (p : Expr pqxdhOps Γ muPendTy) (b : Expr pqxdhOps Γ .bool) : Expr pqxdhOps Γ muStTy :=
  .pair k (.pair c (.pair p b))

def emptyMuE : Expr pqxdhOps Γ muStTy := muMk .nil .nil .nil (.bool false)

def etmBodyE (ct : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 32) :=
  bytesTake 32 (.sub (bytesLen 32 ct) (.nat 8)) ct

def etmBody24E (ct : Expr pqxdhOps Γ (B 24)) : Expr pqxdhOps Γ (B 24) :=
  bytesTake 24 (.sub (bytesLen 24 ct) (.nat 8)) ct

def etmTagE (ct : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 32) :=
  bytesDrop 32 (.sub (bytesLen 32 ct) (.nat 8)) ct

def macInputE (ad : Expr pqxdhOps Γ (B 158)) (ct : Expr pqxdhOps Γ (B 32)) : Expr pqxdhOps Γ (B 359) :=
  catB 201 158
    (catB 158 43
      (bytesTake 158 (.nat firstMsgHdrLen) ad)
      (bytesCons ((8 * 4 + 2 : Nat).toUInt8) 42
        (catB 10 32 (bytesVarint (bytesLen 32 ct)) ct)))
    (bytesDrop 158 (.nat firstMsgHdrLen) ad)

def initSlotE (S : Setup) (sid : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ .nat :=
  eCaseSum sid
    (fun ui => .add (.mulK (if S.N_id = 0 then 0 else S.N_send_opk) (.fst (v ui))) (.snd (v ui)))
    fun r1 => eCaseSum (v r1)
      (fun ui => .add (.nat S.N_send_opk_tot)
        (.add (.mulK (if S.N_id = 0 then 0 else S.N_send_no_opk) (.fst (v ui))) (.snd (v ui))))
      fun _ => .nat S.N_send_tot

def muKeyIdEq {Γ : List PT} (a b : Expr pqxdhOps Γ muKeyIdTy) : Expr pqxdhOps Γ .bool :=
  eLet2 a b fun a b => eCaseSum (v a)
    (fun x => eCaseSum (v b) (fun y => sidEq (v x) (v y)) fun _ => .bool false)
    (fun x => eCaseSum (v b) (fun _ => .bool false) fun y => natEq (v x) (v y))

def initKeyIdE (_ : Setup) (sid : Expr pqxdhOps Γ sessionIdTy) : Expr pqxdhOps Γ muKeyIdTy :=
  eCaseSum sid
    (fun ui => .inl (.inl (v ui)))
    fun r1 => eCaseSum (v r1)
      (fun ui => .inl (.inr (.inl (v ui))))
      fun _ => .inr (.nat 0)

def pendFilterE (K : Nat) {Γ₁ : List PT}
    (a : Var Γ₁ (.prod muPendTy (.prod .nat (B 359)))) [Ext Γ₁ Γ] : Expr pqxdhOps Γ muPendTy :=
  .foldrB K (.fst (v a)) .nil
    (.ite (.and (natEq (.fst (.var .zero)) (.fst (.snd (v a))))
        (bytesBeq 359 (.fst (.snd (.var .zero))) (.snd (.snd (v a)))))
      (.var (.succ .zero))
      (.cons (.var .zero) (.var (.succ .zero))))

def pendHitE (K : Nat) {Γ₁ : List PT}
    (a : Var Γ₁ (.prod muPendTy (.prod .nat (.prod (B 359) (B 32))))) [Ext Γ₁ Γ] :
    Expr pqxdhOps Γ .bool :=
  eAny K (.fst (v a)) fun e =>
    .and (.and (natEq (.fst (v e)) (.fst (.snd (v a))))
        (bytesBeq 359 (.fst (.snd (v e))) (.fst (.snd (.snd (v a))))))
      (bytesBeq 32 (.snd (.snd (v e)))
        (bytesTake 32 (.nat 8) (.snd (.snd (.snd (v a))))))

def dedupE (K : Nat) {Γ₁ : List PT} (xs : Var Γ₁ (.list (.prod .nat (B 359)))) [Ext Γ₁ Γ] :
    Expr pqxdhOps Γ (.list (.prod .nat (B 359))) :=
  .foldrB K (v xs) .nil
    (.ite (.anyB K (.var (.succ .zero))
        (.and (natEq (.fst (.var (.succ .zero))) (.fst (.var .zero)))
          (bytesBeq 359 (.snd (.var (.succ .zero))) (.snd (.var .zero)))))
      (.var (.succ .zero))
      (.cons (.var .zero) (.var (.succ .zero))))

def ipUEntry (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ principalEntryTy := .fst p
def ipPeer (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ (.opt (.prod .nat principalEntryTy)) :=
  .fst (.snd p)
def ipFim (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ (.prod .bool (.prod .bool (B 32))) :=
  .fst (.snd (.snd p))
def ipFresh (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ .bool := .fst (ipFim p)
def ipIdeal (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ .bool := .fst (.snd (ipFim p))
def ipMsgPlain (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ (B 32) := .snd (.snd (ipFim p))
def ipT3 (p : Expr pqxdhOps Γ intPrepTy) := Expr.snd (.snd (.snd p))
def ipKeys6 (p : Expr pqxdhOps Γ intPrepTy) := Expr.fst (ipT3 p)
def ipDrKey (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ drKeyTy := .fst (.snd (ipT3 p))
def ipRks4 (p : Expr pqxdhOps Γ intPrepTy) := Expr.fst (.snd (.snd (ipT3 p)))
def ipSalt (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ (.opt (B 32)) :=
  .fst (.snd (.snd (.snd (ipT3 p))))
def ipPqMsg (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (ipT3 p)))))
def ipAd (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ (B 158) :=
  .fst (.snd (.snd (.snd (.snd (.snd (ipT3 p))))))
def ipProv (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ provTy :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (ipT3 p)))))))
def ipRoC (p : Expr pqxdhOps Γ intPrepTy) : Expr pqxdhOps Γ (.list (.prod (B 192) drKeyTy)) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (ipT3 p))))))))
def ipRootC (p : Expr pqxdhOps Γ intPrepTy) :
    Expr pqxdhOps Γ (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32)))) :=
  .snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (ipT3 p))))))))

end ExprHelpers

def mapMV {ι : Type} {T : OracleSpec ι}
    {I : Iface pqSig T} {Γ : List PT} {τ₁ τ₂ : PT}
    (K : Nat) (xs : Expr pqxdhOps Γ (.list τ₁))
    (f : Var (τ₁ :: Γ) τ₁ → Comp pqxdhOps I (τ₁ :: Γ) τ₂) : Comp pqxdhOps I Γ (.list τ₂) :=
  .mapM K xs (f .zero)

section HmBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List PT}

/-! ## Multi-Key Game Steps -/

def hmKeyIdC (a : Expr pqxdhOps Δ (.prod muKeyIdTy muStTy)) :
    Comp pqxdhOps pqPrimIface Δ (.prod (.prod .nat msgKeysTy) muStTy) :=
  letV a fun a =>
  letV (.fst (v a)) fun i =>
  letV (.snd (v a)) fun st =>
  caseOptV (eFind K (muKeys (v st)) fun e => muKeyIdEq (.fst (v e)) (v i))
    (bindV (samplePrim .msgKeys80) fun mk =>
      letV (.pair (.len (muKeys (v st))) (v mk)) fun e =>
      .ret (.pair (v e)
        (muMk (.cons (.pair (v i) (v e)) (muKeys (v st))) (muChal (v st)) (muPend (v st))
          (muBad (v st)))))
    fun e => .ret (.pair (.snd (v e)) (v st))

def hmKeyC (a : Expr pqxdhOps Δ (.prod .nat muStTy)) :
    Comp pqxdhOps pqPrimIface Δ (.prod (.prod .nat msgKeysTy) muStTy) :=
  letV a fun a => hmKeyIdC K (.pair (.inr (.fst (v a))) (.snd (v a)))

def encPostC (a : Expr pqxdhOps Δ (.prod encContTy (B 32))) :
    Comp pqxdhOps pqPrimIface Δ (.prod (.opt (B 32)) muStTy) :=
  letV a fun a =>
  letV (.fst (v a)) fun c =>
  letV (.snd (v a)) fun t =>
  letV (.fst (v c)) fun i =>
  letV (.fst (.snd (v c))) fun r =>
  letV (.fst (.snd (.snd (v c)))) fun ad =>
  letV (.fst (.snd (.snd (.snd (v c))))) fun ct =>
  letV (.snd (.snd (.snd (.snd (v c))))) fun st =>
  letV (macInputE (v ad) (etmBodyE (widenB 24 8 (v ct)))) fun x0 =>
  letV (catB 24 8 (etmBody24E (v ct)) (takeKB 32 8 (v t))) fun ct' =>
  letV (.pair (muPend (v st)) (.pair (v r) (v x0))) fun fa =>
  letV (.pair (muPend (v st)) (.pair (v r) (.pair (v x0) (v t)))) fun ha =>
  .ret (.pair (.some (v ct'))
    (muMk (muKeys (v st)) (.cons (.pair (v i) (.pair (v ad) (v ct'))) (muChal (v st)))
      (pendFilterE K fa) (boolOr (muBad (v st)) (pendHitE K ha))))

def hmEncPreIdC (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    Comp pqxdhOps pqPrimIface Δ encPreTy :=
  letV a fun a =>
  letV (.fst (v a)) fun jt =>
  letV (.fst (.snd (v a))) fun i =>
  letV (.fst (.snd (.snd (v a)))) fun ad =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun pt =>
  letV (.snd (.snd (.snd (.snd (v a))))) fun st0 =>
  caseOptV (eFind K (muChal (v st0)) fun e => muKeyIdEq (.fst (v e)) (v i))
    (bindV (hmKeyIdC K (.pair (v i) (v st0))) fun kr =>
     letV (.fst (.fst (v kr))) fun r =>
     letV (.snd (.fst (v kr))) fun mk =>
     letV (.snd (v kr)) fun st =>
     bindV (queryPrim (.aeadEnc 158 32 24) (.pair (v mk) (.pair (v ad) (v pt)))) fun ct =>
     letV (.pair (v i) (.pair (v r) (.pair (v ad) (.pair (v ct) (v st))))) fun c =>
     .ite (natLt (v r) (v jt))
       (bindV (samplePrim .bytes32) fun t =>
        bindV (encPostC K (.pair (v c) (v t))) fun res =>
        .ret (.inl (v res)))
       (.ite (natEq (v r) (v jt))
         (.ret (.inr (v c)))
         (.ret (.inl (.pair (.some (widenB 24 8 (v ct)))
           (muMk (muKeys (v st))
             (.cons (.pair (v i) (.pair (v ad) (widenB 24 8 (v ct)))) (muChal (v st)))
             (muPend (v st)) (muBad (v st))))))))
    fun _ => .ret (.inl (.pair .none (v st0)))

def hmEncPreC (a : Expr pqxdhOps Δ (.prod .nat (.prod .nat (.prod (B 158) (.prod (B 32) muStTy))))) :
    Comp pqxdhOps pqPrimIface Δ encPreTy :=
  letV a fun a =>
  hmEncPreIdC K (.pair (.fst (v a)) (.pair (.inr (.fst (.snd (v a)))) (.snd (.snd (v a)))))

def hmForgeIdC (a : Expr pqxdhOps Δ (.prod .nat (.prod muKeyIdTy (.prod (B 158) (.prod (B 32) muStTy))))) :
    Comp pqxdhOps pqPrimIface Δ muStTy :=
  letV a fun a =>
  letV (.fst (v a)) fun jt =>
  letV (.fst (.snd (v a))) fun i =>
  letV (.fst (.snd (.snd (v a)))) fun ad =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun ct =>
  letV (.snd (.snd (.snd (.snd (v a))))) fun st0 =>
  .ite (eCaseOpt (eFind K (muChal (v st0)) fun e => muKeyIdEq (.fst (v e)) (v i)) (.bool false)
      fun e => .and (bytesBeq 158 (.fst (.snd (v e))) (v ad))
        (bytesBeq 32 (.snd (.snd (v e))) (v ct)))
    (.ret (v st0)) <|
  bindV (hmKeyIdC K (.pair (v i) (v st0))) fun kr =>
  letV (.fst (.fst (v kr))) fun r =>
  letV (.snd (.fst (v kr))) fun mk =>
  letV (.snd (v kr)) fun st =>
  letV (macInputE (v ad) (etmBodyE (v ct))) fun x =>
  letV (eCaseOpt (eFind K (muChal (v st)) fun e => muKeyIdEq (.fst (v e)) (v i)) (.bool true)
      fun e => .not (bytesBeq 359 (v x)
        (macInputE (.fst (.snd (v e))) (etmBodyE (.snd (.snd (v e))))))) fun fresh =>
  .ite (.and (v fresh) (natLe (.nat 24) (bytesLen 32 (v ct))))
    (.ite (natLe (v r) (v jt))
      (.ret (muMk (muKeys (v st)) (muChal (v st))
        (.cons (.pair (v r) (.pair (v x) (etmTagE (v ct)))) (muPend (v st))) (muBad (v st))))
      (bindV (queryPrim (.aeadDec 158 32 32) (.pair (v mk) (.pair (v ad) (v ct)))) fun res =>
        .ret (muMk (muKeys (v st)) (muChal (v st)) (muPend (v st))
          (boolOr (muBad (v st)) (isSomeE (v res))))))
    (.ret (v st))

def hmForgeC (a : Expr pqxdhOps Δ (.prod .nat (.prod .nat (.prod (B 158) (.prod (B 32) muStTy))))) :
    Comp pqxdhOps pqPrimIface Δ muStTy :=
  letV a fun a =>
  hmForgeIdC K (.pair (.fst (v a)) (.pair (.inr (.fst (.snd (v a)))) (.snd (.snd (v a)))))

/-! ## Initiator Send Branches -/

def finishIntC (a : Expr pqxdhOps Δ intFinArgsTy) : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV a fun a =>
  letV (.fst (v a)) fun fhst =>
  letV (.fst (.snd (v a))) fun sid =>
  letV (.fst (.snd (.snd (v a)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun m01 =>
  letV (.fst (.snd (.snd (.snd (.snd (v a)))))) fun p =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v a))))))) fun mks =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))) fun aeadCt =>
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (ipUEntry (v p)) fun uE =>
  letV (ipPeer (v p)) fun pp =>
  letV (ipFresh (v p)) fun fresh =>
  letV (ipIdeal (v p)) fun isIdeal =>
  letV (ipMsgPlain (v p)) fun msgPlain =>
  letV (ipKeys6 (v p)) fun keys6 =>
  letV (ipDrKey (v p)) fun drKey =>
  letV (ipRks4 (v p)) fun rks4 =>
  letV (ipSalt (v p)) fun spqrSalt? =>
  letV (ipPqMsg (v p)) fun pqMsg =>
  letV (ipAd (v p)) fun ad =>
  letV (ipProv (v p)) fun prov =>
  letV (ipRoC (v p)) fun roC =>
  letV (ipRootC (v p)) fun rootC =>
  letV (.fst (v keys6)) fun ekASk =>
  letV (.fst (.snd (v keys6))) fun ekAPk =>
  letV (.fst (.snd (.snd (v keys6)))) fun ss =>
  letV (.fst (.snd (.snd (.snd (v keys6))))) fun kemCt =>
  letV (.fst (.snd (.snd (.snd (.snd (v keys6)))))) fun ephASk =>
  letV (.snd (.snd (.snd (.snd (.snd (v keys6)))))) fun ephAPk =>
  letV (.fst (v rks4)) fun rk1 =>
  letV (.fst (.snd (v rks4))) fun ck1_0 =>
  letV (.fst (.snd (.snd (v rks4)))) fun mkSeed =>
  letV (.snd (.snd (.snd (v rks4)))) fun ck1_1 =>
  letV (hdMk (peIkAPk (v uE)) (v ekAPk) (pkbSpkId (v bu)) (optFst (pkbOpkB? (v bu)))
      (pkbPqspkId (v bu)) (v kemCt)) fun hdr =>
  letV (pmMk (v hdr) (v ephAPk) (v pqMsg) (v aeadCt)) fun wireMsg =>
  letV (seMk (v sid) (pkbIkB (v bu)) (pkbSpkB (v bu)) (optSnd (pkbOpkB? (v bu)))
      (pkbPqspkB (v bu)) (.fst (v prov)) (.fst (.snd (v prov))) (.snd (.snd (v prov)))
      (v ekASk) (v ephASk) (v fresh)
      (.and (v fresh) (.not (bytesBeq 32 (.fst (v m01)) (.snd (v m01)))))) fun sessE =>
  letV (ikrMk (v sid) (pkbPqspkB (v bu)) (v kemCt) (v ss)) fun initRec =>
  letV (.ite (v isIdeal)
      (.cons (iasMk (v sid) (peIkAPk (v uE)) (pkbIkB (v bu)) (pkbSpkB (v bu))
        (optSnd (pkbOpkB? (v bu))) (v ekAPk) (pkbPqspkB (v bu)) (v kemCt) (v ephAPk)
        (v spqrSalt?) (v pqMsg) (v ad) (v aeadCt) (v msgPlain) (v drKey)
        (v rk1) (v ck1_0) (v mkSeed) (v ck1_1) (v mks)) (ahsIdealSessions (v hst)))
      (ahsIdealSessions (v hst))) fun idealS' =>
  letV (ahsUpd (v hst)
      (base := stUpd (v st)
        (sess := .cons (v sessE) (asSessions (v st)))
        (usedS := .cons (v sid) (asUsedSendSessions (v st)))
        (ro := v roC) (root := v rootC))
      (initR := .cons (v initRec) (ahsInitKemRecs (v hst)))
      (idealS := v idealS')) fun hst' =>
  letV (.ite (isSomeE (v pp)) (aSendFresh (v wireMsg))
      (aSendUnfresh (v drKey) (v rk1) (v ck1_1) (v wireMsg))) fun resp =>
  .ret (.pair (v resp) (ahsfUpd (v fhst) (hst := v hst')))

def intSendPrepC (opk : Bool) (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt intPrepTy) :=
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret .none) <|
  .ite (eAny K (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)) (.ret .none) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret .none) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1)))) (.ret .none) <|
  letV (.ite (v isFresh) (.ite (asSecb (v st)) (v m1) (v m0)) (v m0)) fun msgPlain =>
  bindV (koskBundleOkC S K st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret .none) <|
  bindV (samplePrim .bytes32) fun ekASk =>
  bindV (samplePrim .bytes32) fun kemCoins =>
  bindV (samplePrim .bytes32) fun ephASk =>
  bindV (samplePrim .bytes32) fun spqrCoins =>
  letV (eCaseOpt (v pp) (pkbIkB (v bu)) fun p => peIkSignPk (.snd (v p))) fun sigPkB =>
  bindV (queryPrim (.sigVerify 33)
      (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu)))))
    fun v1 =>
  bindV (queryPrim (.sigVerify 1569)
      (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu)))))
    fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret .none) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret .none) fun sc =>
  letV (.fst (v sc)) fun ss =>
  letV (.snd (v sc)) fun kemCt =>
  bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
  bindV (checkBundleProvenanceExactC S K st bu) fun prov =>
  bindV (spkHonIdealFromPeerC S K st pp bu) fun spkHonIdeal =>
  letV (boolOr (v isFresh)
      (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (.snd (.snd (v prov)))))
    fun isIdealSend =>
  bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (getDBytes (optSnd (pkbOpkB? (v bu))))))
    fun dh4Raw =>
  letV (eCaseOpt (pkbOpkB? (v bu)) .none fun _ => .some (v dh4Raw)) fun dh4? =>
  letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
  bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
  bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .drKey96) fun dk => .ret (.pair (v dk) (asRoCache (v st))))
      (hkdfRoC K st (v secrets))) fun drOut =>
  letV (.fst (v drOut)) fun drKey =>
  letV (.snd (v drOut)) fun roC' =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
        .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))
      (rootRoC K st (.fst (v drKey)) (v dhR))) fun rkOut =>
  letV (.fst (.fst (v rkOut))) fun rk1 =>
  letV (.snd (.fst (v rkOut))) fun ck1_0 =>
  letV (.snd (v rkOut)) fun rootC' =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
        .ret (.pair (v ms) (v cn)))
      (bindV (queryPrim .chainKdfSeed (v ck1_0)) fun ms =>
       bindV (queryPrim .chainKdfNext (v ck1_0)) fun cn => .ret (.pair (v ms) (v cn)))) fun mkc =>
  letV (.fst (v mkc)) fun mkSeed =>
  letV (.snd (v mkc)) fun ck1_1 =>
  bindV (queryPrim (.spqrInitSend 32 32) (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
  caseOptV (v sp?) (.ret .none) fun sp =>
  letV (.fst (.snd (v sp))) fun spqrSalt? =>
  letV (.snd (.snd (v sp))) fun pqMsg =>
  letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
  .ret (.some (.pair (v uE) (.pair (v pp) (.pair (.pair (v isFresh)
      (.pair (v isIdealSend) (v msgPlain)))
    (.pair (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ss) (.pair (v kemCt)
        (.pair (v ephASk) (v ephAPk))))))
      (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
        (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v ad) (.pair (v prov)
          (.pair (v roC') (v rootC')))))))))))))

def sendSidE (opk : Bool) {Γ : List PT} (x : Expr pqxdhOps Γ sendQTy) : Expr pqxdhOps Γ sessionIdTy :=
  if opk then .inl (.pair (.fst x) (.fst (.snd x)))
  else .inr (.inl (.pair (.fst x) (.fst (.snd x))))

def hmSendTailC (opk : Bool) (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy) (p : Var Γ₅ intPrepTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] : Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  letV (sendSidE opk (v x)) fun sid =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.snd (.snd (.snd (v x)))) fun m01 =>
  letV (ipAd (v p)) fun ad =>
  letV (ipMsgPlain (v p)) fun msgPlain =>
  .ite (ipIdeal (v p))
    (bindV (hmEncPreIdC K (.pair (v jt) (.pair (initKeyIdE S (v sid)) (.pair (v ad)
        (.pair (v msgPlain) (v mst)))))) fun e =>
     caseSumV (v e)
       (fun l =>
         bindV (finishIntC (.pair (v fhst) (.pair (v sid) (.pair (v bu) (.pair (v m01)
             (.pair (v p) (.pair defaultMsgKeysE (getDBytes (.fst (v l)))))))))) fun r =>
         .ret (.inl (.pair (v r) (.snd (v l)))))
       (fun c => .ret (.inr (.pair (v sid) (.pair (v bu) (.pair (v m01) (.pair (v p)
         (.pair (v fhst) (v c)))))))))
    (bindV (queryPrim (.deriveMsgKeys 32)
         (.pair (.fst (.snd (.snd (ipRks4 (v p))))) (ipSalt (v p))))
       fun mk =>
     bindV (queryPrim (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad) (v msgPlain)))) fun ct =>
     bindV (finishIntC (.pair (v fhst) (.pair (v sid) (.pair (v bu) (.pair (v m01)
         (.pair (v p) (.pair (v mk) (v ct)))))))) fun r =>
     .ret (.inl (.pair (v r) (v mst))))

def hmSendC (opk : Bool) (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  .ite (sendGuardE opk (v x)) (.ret (.inl (.pair (.pair aNone (v fhst)) (v mst)))) <|
  bindV (intSendPrepC S K opk fhst x) fun p? =>
  caseOptV (v p?) (.ret (.inl (.pair (.pair aNone (v fhst)) (v mst)))) fun p =>
  hmSendTailC S K opk jt fhst mst x p

/-! ## Responder Receive Branches -/

def hmRecvPrepC (opk : Bool) (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt hmRecvDataTy) :=
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pkmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  .ite (.not (.and (.and (.and (.and (.and
      (u32Beq (hdrSpkId (v hdr)) (u32OfNat (.fst (.snd (v x)))))
      (u32Beq (hdrPqspkId (v hdr)) (u32OfNat (.fst (.snd (v x))))))
      (optU32Eq (hdrOpkId? (v hdr))
        (if opk then .some (u32OfNat (.fst (.snd (.snd (v x))))) else .none)))
      (natEq (bytesLen 32 (hdrIkAPk (v hdr))) (.nat 32)))
      (natEq (bytesLen 32 (hdrEkAPk (v hdr))) (.nat 32)))
      (natEq (bytesLen 32 (pkmEphAPk (v msg))) (.nat 32))))
    (.ret .none) <|
  .ite (eAny K (if opk then asUsedRecvOPK (v st) else asUsedRecvNoOPK (v st))
      fun e => nat3Eq (v e) (v kjo))
    (.ret .none) <|
  bindV (koskSenderOkC S K st (hdrIkAPk (v hdr))) fun koskOk =>
  .ite (.not (v koskOk)) (.ret .none) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret .none) fun kPair =>
  caseOptV (eFind K (asSpkBundles (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret .none) fun bPair =>
  letV (.snd (v kPair)) fun kE =>
  letV (.snd (v bPair)) fun bE =>
  bindV (if opk then
      caseOptV (eFind K (asOpkEntries (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
        (.ret (.inl .unit)) fun oPair =>
      .ite (oeConsumed (.snd (v oPair))) (.ret (.inl .unit))
        (.ret (.inr (.some (.snd (v oPair)))))
    else .ret (.inr .none) : Comp pqxdhOps pqPrimIface _ (.sum .unit (.opt opkEntryTy))) fun oRes =>
  caseSumV (v oRes) (fun _ => .ret .none) fun oE? =>
  letV (kyberCheckE K (asUsedKyberTriples (v st)) (.pair (.fst (v x)) (.pair (hdrPqspkId (v hdr))
      (.pair (hdrSpkId (v hdr)) (hdrEkAPk (v hdr)))))) fun kc =>
  bindV (queryPrim .isCanonical (hdrEkAPk (v hdr))) fun can =>
  bindV (queryPrim .isCanonical (pkmEphAPk (v msg))) fun canE =>
  .ite (boolOr (boolOr (.not (.fst (v kc))) (.not (v can))) (.not (v canE)))
    (.ret .none) <|
  bindV (queryPrim .kemDecaps (.pair (sbPqspkSk (v bE)) (hdrKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret .none) fun ss =>
  letV (rkrMk (.fst (v x)) (.fst (.snd (v x))) (sbPqspkPk (v bE)) (sbPqspkSk (v bE))
      (hdrKemCt (v hdr)) (v ss)) fun rRec =>
  letV (ahsUpd (v hst) (recvR := .cons (v rRec) (ahsRecvKemRecs (v hst)))) fun hstDec =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrIkAPk (v hdr)))) fun dh1 =>
  bindV (queryPrim .x25519 (.pair (peSecIKA0 (v kE)) (hdrEkAPk (v hdr)))) fun dh2 =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrEkAPk (v hdr)))) fun dh3 =>
  bindV (caseOptV (v oE?) (.ret .none) fun oE =>
      bindV (queryPrim .x25519 (.pair (oeOpkSk (v oE)) (hdrEkAPk (v hdr)))) fun dh4 =>
      .ret (.some (v dh4))) fun dh4? =>
  letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
  bindV (findHonestC S K st (hdrIkAPk (v hdr))) fun snd? =>
  .ret (.some (.pair (v kE) (.pair (v bE)
    (.pair (eCaseOpt (v oE?) .none fun oE => .some (oeOpkPk (v oE)))
      (.pair (v secrets) (.pair (v hstDec) (.pair (.snd (v kc)) (isSomeE (v snd?)))))))))

def hmSchedPrepC (a : Expr pqxdhOps Δ schedPrepArgsTy) : Comp pqxdhOps pqPrimIface Δ (.opt schedPrepTy) :=
  letV a fun a =>
  letV (.fst (v a)) fun hstDec =>
  letV (.fst (.snd (v a))) fun kE =>
  letV (.fst (.snd (.snd (v a)))) fun bE =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun opkBPk? =>
  letV (.fst (.snd (.snd (.snd (.snd (v a)))))) fun secrets =>
  letV (.snd (.snd (.snd (.snd (.snd (v a)))))) fun msg =>
  letV (ahsBase (v hstDec)) fun st =>
  letV (pkmHdr (v msg)) fun hdr =>
  bindV (findHonestC S K st (hdrIkAPk (v hdr))) fun snd? =>
  letV (eCaseOpt (v snd?) (.bool false) fun sP => .not (peCorrupted (.snd (v sP))))
    fun isUncorr =>
  letV (peIkAPk (v kE)) fun ikBPk =>
  letV (sbSpkPk (v bE)) fun spkBPk =>
  letV (sbPqspkPk (v bE)) fun pqspkBPk =>
  bindV (findMV (min K S.N_sess_tot) (ahsIdealSessions (v hstDec)) fun s =>
      matchIdealAuthHandshakeC ikBPk spkBPk opkBPk? pqspkBPk hdr s) fun matched? =>
  letV (boolOr (isSomeE (v matched?)) (v isUncorr)) fun useIdeal =>
  bindV (.ite (v useIdeal)
      (caseOptV (v matched?)
        (bindV (samplePrim .drKey96) fun dk => .ret (.pair (v dk) (asRoCache (v st))))
        fun s => .ret (.pair (iasDrKey (v s)) (asRoCache (v st))))
      (hkdfRoC K st (v secrets))) fun drOut =>
  letV (.fst (v drOut)) fun drKey =>
  letV (.snd (v drOut)) fun roC' =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pkmEphAPk (v msg)))) fun dhR =>
  bindV (caseOptV (v matched?) (.ret (.bool false)) fun s =>
      bindV (queryPrim .pow8 (pkmEphAPk (v msg))) fun p1 =>
      bindV (queryPrim .pow8 (iasEphAPk (v s))) fun p2 =>
      .ret (bytesBeq 32 (v p1) (v p2))) fun sameEph =>
  bindV (.ite (v useIdeal)
      (caseOptV (v matched?)
        (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
          .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))
        fun s => .ite (v sameEph)
          (.ret (.pair (.pair (iasRk1 (v s)) (iasCk1_0E (v s))) (asRootRoCache (v st))))
          (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
            .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st)))))
      (rootRoC K st (.fst (v drKey)) (v dhR))) fun rkOut =>
  letV (.fst (.fst (v rkOut))) fun rk1 =>
  letV (.snd (.fst (v rkOut))) fun ck1_0 =>
  letV (.snd (v rkOut)) fun rootC' =>
  bindV (.ite (v useIdeal)
      (caseOptV (v matched?)
        (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
          .ret (.pair (v ms) (v cn)))
        fun s => .ite (v sameEph)
          (.ret (.pair (iasMkSeed (v s)) (iasCk1_1 (v s))))
          (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
            .ret (.pair (v ms) (v cn))))
      (bindV (queryPrim .chainKdfSeed (v ck1_0)) fun ms =>
       bindV (queryPrim .chainKdfNext (v ck1_0)) fun cn => .ret (.pair (v ms) (v cn))))
    fun mkc =>
  letV (.fst (v mkc)) fun mkSeed =>
  letV (.snd (v mkc)) fun ck1_1 =>
  bindV (queryPrim (.spqrInitRecv 32 32)
      (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
  caseOptV (v sp?) (.ret .none) fun sp =>
  .ret (.some (.pair (v isUncorr) (.pair (v matched?) (.pair (v useIdeal) (.pair (v drKey)
    (.pair (v roC') (.pair (v sameEph) (.pair (v rk1) (.pair (v ck1_0) (.pair (v rootC')
      (.pair (v mkSeed) (.pair (v ck1_1) (.snd (v sp))))))))))))))

def forgeRetIdC (fc : Var Γ₁ (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))) [Ext Γ₁ Δ]
    (idx : Expr pqxdhOps Δ muKeyIdTy) (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) :
    Comp pqxdhOps pqPrimIface Δ schedResTy :=
  letV (.pair idx cache') fun ic =>
  bindV (hmForgeIdC K (.pair (.fst (v fc)) (.pair (.fst (v ic)) (.snd (v fc))))) fun mst' =>
  .ret (.pair (.pair .none (.snd (v ic))) (v mst'))

def forgeRetC (fc : Var Γ₁ (.prod .nat (.prod (B 158) (.prod (B 32) muStTy)))) [Ext Γ₁ Δ]
    (idx : Expr pqxdhOps Δ .nat) (cache' : Expr pqxdhOps Δ authMkSaltCacheTy) :
    Comp pqxdhOps pqPrimIface Δ schedResTy :=
  forgeRetIdC K fc (.inr idx) cache'

def hmSchedFinC (a : Expr pqxdhOps Δ schedFinArgsTy) : Comp pqxdhOps pqPrimIface Δ schedResTy :=
  letV a fun a =>
  letV (.fst (v a)) fun jt =>
  letV (.fst (.snd (v a))) fun kE =>
  letV (.fst (.snd (.snd (v a)))) fun msg =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun rc =>
  letV (.fst (.snd (.snd (.snd (.snd (v a)))))) fun cache =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v a))))))) fun sp =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (v a))))))) fun mst =>
  letV (.fst (.snd (v sp))) fun matched? =>
  letV (.fst (.snd (.snd (v sp)))) fun useIdeal =>
  letV (.fst (.snd (.snd (.snd (v sp))))) fun drKey =>
  letV (.fst (.snd (.snd (.snd (.snd (v sp)))))) fun roC' =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v sp))))))) fun sameEph =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (v sp)))))))) fun rk1 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v sp)))))))))) fun rootC' =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v sp))))))))))) fun mkSeed =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (v sp)))))))))))) fun ck1_1 =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (v sp)))))))))))) fun salt? =>
  letV (eCaseOpt (v matched?) (.bool false) fun s =>
      .and (v sameEph) (sameSaltKeyE (v salt?) (iasSpqrSalt? (v s)))) fun sameMk =>
  letV (firstMsgADE (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (v kE)) (pkmEphAPk (v msg))
      (pkmPqRatchetMsg (v msg))) fun ad =>
  letV (.pair (v jt) (.pair (v ad) (.pair (pkmAeadCt (v msg)) (v mst)))) fun fc =>
  .ite (v useIdeal)
    (caseOptV (v matched?)
      (forgeRetIdC K fc (.inr (v rc)) (v cache))
      fun s =>
        .ite (v sameMk)
          (.ite (.and (bytesBeq 158 (v ad) (iasAdE (v s)))
              (bytesBeq 32 (pkmAeadCt (v msg)) (iasAeadCtE (v s))))
            (.ret (.pair (.pair (.some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
                (.pair (iasMsgPlainE (v s)) (.pair (v roC') (v rootC')))))))
              (v cache)) (v mst)))
            (forgeRetIdC K fc (initKeyIdE S (iasSid (v s))) (v cache)))
          (.ite (v sameEph)
            (caseOptV (eFind K (v cache) fun e =>
                .and (sidEq (.fst (.fst (v e))) (iasSid (v s)))
                  (sameSaltKeyE (.snd (.fst (v e))) (v salt?)))
              (forgeRetIdC K fc (.inr (v rc))
                (.cons (.pair (.pair (iasSid (v s)) (v salt?)) (.pair (v rc) defaultMsgKeysE))
                  (v cache)))
              fun e => forgeRetIdC K fc (.inr (.fst (.snd (v e))))
                (v cache))
            (forgeRetIdC K fc (.inr (v rc)) (v cache))))
    (bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v salt?))) fun mk =>
     bindV (queryPrim (.aeadDec 158 32 32) (.pair (v mk) (.pair (v ad) (pkmAeadCt (v msg)))))
       fun pt? =>
     caseOptV (v pt?) (.ret (.pair (.pair .none (v cache)) (v mst))) fun pt =>
     .ret (.pair (.pair (.some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
         (.pair (v pt) (.pair (v roC') (v rootC')))))))
       (v cache)) (v mst)))

def hmSchedC (a : Expr pqxdhOps Δ schedArgsTy) : Comp pqxdhOps pqPrimIface Δ schedResTy :=
  letV a fun a =>
  letV (.fst (v a)) fun jt =>
  letV (.fst (.snd (v a))) fun rc =>
  letV (.fst (.snd (.snd (v a)))) fun cache =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun pa =>
  letV (.snd (.snd (.snd (.snd (v a))))) fun mst =>
  bindV (hmSchedPrepC S K (v pa)) fun sp? =>
  caseOptV (v sp?) (.ret (.pair (.pair .none (v cache)) (v mst))) fun sp =>
  hmSchedFinC S K (.pair (v jt) (.pair (.fst (.snd (v pa)))
    (.pair (.snd (.snd (.snd (.snd (.snd (v pa))))))
      (.pair (v rc) (.pair (v cache) (.pair (v sp) (v mst)))))))

def finErasedE (opk : Bool) {Γ : List PT} (kjo : Var Γ₁ (.prod .nat (.prod .nat .nat)))
    (usedT' : Var Γ₂ (.list (.prod .nat (.prod U32 (.prod U32 (B 32))))))
    (sndHon : Var Γ₃ .bool) (hstDec : Var Γ₄ authHybridStateTy) (res? : Var Γ₅ schedOutTy)
    [Ext Γ₁ Γ] [Ext Γ₂ Γ] [Ext Γ₃ Γ] [Ext Γ₄ Γ] [Ext Γ₅ Γ] : Expr pqxdhOps Γ RSH :=
  eCaseOpt (v res?) (.pair aNone (v hstDec)) fun r =>
    .pair
      (.ite (v sndHon) aRecvHonest
        (aRecvUnfresh (.fst (v r)) (.fst (.snd (v r))) (.fst (.snd (.snd (v r))))
          (.fst (.snd (.snd (.snd (v r)))))))
      (ahsUpd (v hstDec) (base :=
        if opk then
          stUpd (ahsBase (v hstDec))
            (opks := eMap K (asOpkEntries (ahsBase (v hstDec))) fun e =>
              .ite (nat3Eq (.fst (v e)) (v kjo))
                (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .bool true))) (v e))
            (usedO := .cons (v kjo) (asUsedRecvOPK (ahsBase (v hstDec))))
            (kyb := v usedT') (ro := .fst (.snd (.snd (.snd (.snd (v r))))))
            (root := .snd (.snd (.snd (.snd (.snd (v r))))))
        else
          stUpd (ahsBase (v hstDec))
            (usedN := .cons (v kjo) (asUsedRecvNoOPK (ahsBase (v hstDec))))
            (kyb := v usedT') (ro := .fst (.snd (.snd (.snd (.snd (v r))))))
            (root := .snd (.snd (.snd (.snd (.snd (v r))))))))

def hmRecvTailC (opk : Bool) (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] : Comp pqxdhOps pqPrimIface Δ hmResTy :=
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  letV (.fst (v d)) fun kE =>
  letV (.fst (.snd (v d))) fun bE =>
  letV (.fst (.snd (.snd (v d)))) fun opkPk? =>
  letV (.fst (.snd (.snd (.snd (v d))))) fun secrets =>
  letV (.fst (.snd (.snd (.snd (.snd (v d)))))) fun hstDec =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v d))))))) fun usedT' =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (v d))))))) fun sndHon =>
  bindV (hmSchedC S K (.pair (v jt) (.pair (ahsfRecvCount (v fhst))
      (.pair (ahsfMkSaltCache (v fhst))
        (.pair (.pair (v hstDec) (.pair (v kE) (.pair (v bE) (.pair (v opkPk?)
          (.pair (v secrets) (v msg)))))) (v mst)))))) fun so =>
  letV (.fst (.fst (v so))) fun res? =>
  letV (.snd (.fst (v so))) fun cache' =>
  letV (.snd (v so)) fun mst' =>
  letV (finErasedE K opk kjo usedT' sndHon hstDec res?) fun fin =>
  .ret (.pair (.pair (.fst (v fin))
      (ahsfMk (.snd (v fin)) (.add (ahsfRecvCount (v fhst)) (.nat 1)) (v cache')))
    (v mst'))

def hmRecvC (opk : Bool) (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  bindV (hmRecvPrepC S K opk fhst x) fun d? =>
  caseOptV (v d?)
    (.ret (.inl (.pair (.pair aNone
      (ahsfUpd (v fhst) (rc := .add (ahsfRecvCount (v fhst)) (.nat 1)))) (v mst))))
    fun d =>
  bindV (hmRecvTailC S K opk jt fhst mst x d) fun r => .ret (.inl (v r))

/-! ## Query Dispatch and Reduction Program -/

def hmOther (mst : Var Γ₁ muStTy) [Ext Γ₁ Δ] (m : Comp pqxdhOps pqPrimIface Δ RSF) :
    Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  bindV m fun r => .ret (.inl (.pair (v r) (v mst)))

def hmDispatchC (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy) (mst : Var Γ₃ muStTy)
    (q : Var Γ₄ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  caseSumV (v q) (fun u => hmOther mst (initPrinFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun u => hmOther mst (corruptFixedB K fhst u)) fun q =>
  caseSumV (v q) (fun x => hmOther mst (genSpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => hmOther mst (genOpkFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun x => hmSendC S K true jt fhst mst x) fun q =>
  caseSumV (v q) (fun x => hmSendC S K false jt fhst mst x) fun q =>
  caseSumV (v q) (fun x => hmRecvC S K true jt fhst mst x) fun q =>
  caseSumV (v q) (fun x => hmRecvC S K false jt fhst mst x) fun q =>
  caseSumV (v q) (fun sec => hmOther mst (roFixedB K fhst sec)) fun q =>
  caseSumV (v q) (fun x => hmOther mst (roRootFixedB K fhst x)) fun q =>
  caseSumV (v q) (fun _ => .ret (.inl (.pair (.pair aNone (v fhst)) (v mst)))) fun sk =>
  hmOther mst (registerFixedB fhst sk)

def hmPostC (a : Expr pqxdhOps Δ (.prod hmSendContTy (B 32))) : Comp pqxdhOps pqPrimIface Δ hmResTy :=
  letV a fun a =>
  letV (.fst (v a)) fun c =>
  letV (.snd (v a)) fun t =>
  letV (.fst (v c)) fun sid =>
  letV (.fst (.snd (v c))) fun bu =>
  letV (.fst (.snd (.snd (v c)))) fun m01 =>
  letV (.fst (.snd (.snd (.snd (v c))))) fun p =>
  letV (.fst (.snd (.snd (.snd (.snd (v c)))))) fun fhst =>
  letV (.snd (.snd (.snd (.snd (.snd (v c)))))) fun enc =>
  bindV (encPostC K (.pair (v enc) (v t))) fun ep =>
  bindV (finishIntC (.pair (v fhst) (.pair (v sid) (.pair (v bu) (.pair (v m01)
      (.pair (v p) (.pair defaultMsgKeysE (getDBytes (.fst (v ep)))))))))) fun r =>
  .ret (.pair (v r) (.snd (v ep)))

end HmBranches

section Prog

variable (S : Setup) (K : Nat)

def hmPreC : Comp pqxdhOps pqPrimIface [hmStTy, authQueryTy] hmPreTy :=
  letV (.var .zero : Expr pqxdhOps [hmStTy, authQueryTy] hmStTy) fun s =>
  letV (.fst (v s)) fun jt =>
  letV (.fst (.snd (v s))) fun fhst =>
  letV (.snd (.snd (v s))) fun mst =>
  hmDispatchC S K jt fhst mst
    (.succ (.succ (.succ (.succ (.succ .zero)))) :
      Var [muStTy, authHybridStateFixedTy, .nat, hmStTy, hmStTy, authQueryTy] authQueryTy)

def hmContX0E {Γ : List PT} (c : Expr pqxdhOps Γ hmSendContTy) : Expr pqxdhOps Γ (B 359) :=
  macInputE (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd c))))))))
    (etmBodyE (widenB 24 8 (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd c)))))))))))

def hmInitC : Comp pqxdhOps pqPrfHmacIface [.unit] (.prod .unit hmStTy) :=
  bindV (sampleChal (.index (S.N_send_tot + S.N_recv_tot))) fun jt =>
  bindV (sampleChal .bool) fun secb =>
  .ret (.pair .unit (.pair (v jt) (.pair (emptyAuthHybridStFixedE (v secb)) emptyMuE)))

def hmHandleC : Comp pqxdhOps pqPrfHmacIface [hmStTy, authQueryTy] (.prod authRespTy hmStTy) :=
  bindV (liftPrimComp (hmPreC S K)) fun pre =>
  letV (.fst (.var (.succ .zero)) : Expr pqxdhOps [hmPreTy, hmStTy, authQueryTy] .nat) fun jt =>
  caseSumV (v pre)
    (fun r => .ret (.pair (.fst (.fst (v r)))
      (.pair (v jt) (.pair (.snd (.fst (v r))) (.snd (v r))))))
    fun c =>
      bindV (queryHmacEval (hmContX0E (v c))) fun t =>
      bindV (liftPrimComp (hmPostC K (.pair (v c) (v t)))) fun r =>
      .ret (.pair (.fst (.fst (v r)))
        (.pair (v jt) (.pair (.snd (.fst (v r))) (.snd (v r)))))

def hmFinishC : Comp pqxdhOps pqPrfHmacIface [hmStTy, .bool] .bool :=
  letV (.snd (.snd (.var .zero)) : Expr pqxdhOps [hmStTy, .bool] muStTy) fun mst =>
  letV (.fst (.var (.succ .zero)) : Expr pqxdhOps [muStTy, hmStTy, .bool] .nat) fun jt =>
  letV (muPend (v mst)) fun pend =>
  letV (eMap K (v pend) fun e => .pair (.fst (v e)) (.fst (.snd (v e)))) fun pts0 =>
  letV (dedupE K pts0) fun pts =>
  bindV (mapMV K (v pts) fun pt =>
      bindV (.ite (natLt (.fst (v pt)) (v jt)) (sampleChal .bytes32)
        (queryHmacEval (.snd (v pt)))) fun t =>
      letV (.pair (v pend) (.pair (.fst (v pt)) (.pair (.snd (v pt)) (v t)))) fun ha =>
      .ret (pendHitE K ha)) fun hits =>
  .ret (boolOr (muBad (v mst)) (eAny K (v hits) fun h => v h))

/-- `ReductionDsl` witness for `prfHmacReductionAuth` with list-traversal bound `K`. -/
def prfHmacRedProg :
    CostedReduction pqxdhOps pqPrfHmacIface (authSpec S) (authCodec S) .unit .unit .bool .bool where
  σ      := hmStTy
  init   := hmInitC S
  handle := hmHandleC S K
  finish := hmFinishC K

end Prog

end SignalPqxdh.Security.ReductionDsl.AuthPrfHmac
