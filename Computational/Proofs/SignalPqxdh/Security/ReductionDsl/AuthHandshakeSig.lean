/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshake

/-!
# `ReductionDsl` Program for the `Auth` `SigEufCma` Reduction

Defines `sigReductionAuthProg` and its clamped variant `sigReductionAuthProg2` over
`pqxdhEufCmaIface`, mirroring the shallow reduction `sigReductionAuth`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

/-- Core reduction state `(forgery, targetParty, targetPk, gameState)`. -/
abbrev sigCoreTy : Ty pqSig :=
  .prod (.opt (.prod (B 1569) (B 64))) (.prod .nat (.prod (B 32) authStateTy))
abbrev sigStTy : Ty pqSig := .prod .nat sigCoreTy
abbrev signReqTy : Ty pqSig := .prod (B 32) (.prod (B 32) (.prod .nat (.prod .nat (B 32))))
abbrev sigStepTy : Ty pqSig := .sum (.prod authRespTy sigCoreTy) signReqTy

section SigBranches

variable (S : Setup) (K : Nat) {Γ Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}

def wrapC (m : Comp pqxdhOps pqPrimIface Δ RS)
    (fg : Expr pqxdhOps (RS :: Δ) (.opt (.prod (B 1569) (B 64))))
    (tp : Expr pqxdhOps (RS :: Δ) .nat) (tpk : Expr pqxdhOps (RS :: Δ) (B 32)) :
    Comp pqxdhOps pqPrimIface Δ sigStepTy :=
  bindV m fun r =>
    .ret (.inl (.pair (.fst (v r)) (.pair fg (.pair tp (.pair tpk (.snd (v r)))))))

def extractC (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (bu : Var Γ₄ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ (.opt (.prod (B 1569) (B 64))) :=
  bindV (honestPeerC S K st (buIkB (v bu))) fun peer =>
  bindV (.queryPrim (.sigVerify 33)
      (.pair (v tpk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (.queryPrim (.sigVerify 1569)
      (.pair (v tpk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .ret (eCaseOpt (v peer) .noneE fun k =>
    .ite (natEq (v k) (v tp))
      (.ite (.boolAnd (v v1) (.boolNot (eAny K (stSpks (v st)) fun b =>
          .boolAnd (natEq (.fst (.fst (v b))) (v k))
            (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))))
        (.someE (.pair (.bytesWiden 33 1536 (encEC (buSpkB (v bu)))) (buSpkSig (v bu))))
        (.ite (.boolAnd (v v2) (.boolNot (eAny K (stSpks (v st)) fun b =>
            .boolAnd (natEq (.fst (.fst (v b))) (v k))
              (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))))
          (.someE (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu))))
          .noneE))
      .noneE)

def sigStepC (tp : Var Γ₁ .nat) (tpk : Var Γ₂ (B 32)) (st : Var Γ₃ authStateTy)
    (q : Var Γ₄ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ sigStepTy :=
  caseSumV (v q)
    (fun u =>
      .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u))
        (.ret (.inl (.pair aNone (.pair .noneE (.pair (v tp) (.pair (v tpk) (v st))))))) <|
      .iteC (natEq (v u) (v tp))
        (bindV .sampleBytes32 fun s0 => bindV (.queryPrim .x25519Base (v s0)) fun ik =>
          .ret (.inl (.pair (aInitPrin (v ik) (v tpk)) (.pair .noneE (.pair (v tp) (.pair (v tpk)
            (stUpd (v st) (prin := .listCons
              (.pair (v u) (peMk (v s0) (v ik) (.litBytes 32 []) (v tpk) (.litBool false)))
              (stPrin (v st))))))))))
        (wrapC (initPrinB K st u) .noneE (v tp) (v tpk))) fun q =>
  caseSumV (v q)
    (fun u =>
      .iteC (natEq (v u) (v tp))
        (caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u))
          (.ret (.inl (.pair aNone (.pair .noneE (.pair (v tp) (.pair (v tpk) (v st)))))))
          fun _ => .ret (.inl (.pair aNone (.pair .noneE (.pair (v tp) (.pair (v tpk)
            (stUpd (v st) (prin := eMap K (stPrin (v st)) fun x =>
              .ite (natEq (.fst (v x)) (v u))
                (.pair (.fst (v x)) (peUpd (.snd (v x)) (corrupted := .litBool true)))
                (v x)))))))))
        (wrapC (corruptB K st u) .noneE (v tp) (v tpk))) fun q =>
  caseSumV (v q)
    (fun x =>
      .iteC (natEq (.fst (v x)) (v tp))
        (.iteC (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x))
          (.ret (.inl (.pair aNone (.pair .noneE (.pair (v tp) (.pair (v tpk) (v st))))))) <|
          caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
            (.ret (.inl (.pair aNone (.pair .noneE (.pair (v tp) (.pair (v tpk) (v st)))))))
            fun uE =>
          bindV .sampleBytes32 fun spkSk => bindV (.queryPrim .x25519Base (v spkSk)) fun spkPk =>
          .ret (.inr (.pair (v spkSk) (.pair (v spkPk) (.pair (.fst (v x)) (.pair (.snd (v x))
            (peIkAPk (.snd (v uE)))))))))
        (wrapC (genSpkB K st x) .noneE (v tp) (v tpk))) fun q =>
  caseSumV (v q) (fun x => wrapC (genOpkB K st x) .noneE (v tp) (v tpk)) fun q =>
  caseSumV (v q)
    (fun x =>
      letV (.fst (.snd (.snd (v x)))) fun bu =>
      bindV (extractC S K tp tpk st bu) fun fg =>
      wrapC (sendB S K true st x) (v fg) (v tp) (v tpk)) fun q =>
  caseSumV (v q)
    (fun x =>
      letV (.fst (.snd (.snd (v x)))) fun bu =>
      bindV (extractC S K tp tpk st bu) fun fg =>
      wrapC (sendB S K false st x) (v fg) (v tp) (v tpk)) fun q =>
  caseSumV (v q) (fun x => wrapC (recvB S K true st x) .noneE (v tp) (v tpk)) fun q =>
  caseSumV (v q) (fun x => wrapC (recvB S K false st x) .noneE (v tp) (v tpk)) fun q =>
  caseSumV (v q) (fun sec => wrapC (roB K st sec) .noneE (v tp) (v tpk)) fun q =>
  caseSumV (v q) (fun x => wrapC (roRootB K st x) .noneE (v tp) (v tpk)) fun q =>
  caseSumV (v q)
    (fun _ => .ret (.inl (.pair aNone (.pair .noneE (.pair (v tp) (.pair (v tpk) (v st)))))))
    fun sk => wrapC (registerB st sk) .noneE (v tp) (v tpk)

end SigBranches

def sigHandleDsl (S : Setup) (K : Nat) :
    Comp pqxdhOps pqxdhEufCmaIface [sigStTy, authQueryTy] (.prod authRespTy sigStTy) :=
  letV (.var .vz : Expr pqxdhOps [sigStTy, authQueryTy] sigStTy) fun s =>
  letV (.fst (v s)) fun bud => letV (.snd (v s)) fun core =>
  letV (.fst (v core)) fun fg => letV (.fst (.snd (v core))) fun tp =>
  letV (.fst (.snd (.snd (v core)))) fun tpk => letV (.snd (.snd (.snd (v core)))) fun gs =>
  bindV (Comp.liftChal (C := eufCmaSignOracle) (caseOptV (v fg)
      (sigStepC S K tp tpk gs (.vs .vz : Var [sigStTy, authQueryTy] authQueryTy))
      fun _ => .ret (.inl (.pair aNone (v core))))) fun res =>
  caseSumV (v res)
    (fun d => .ret (.pair (.fst (v d)) (.pair (v bud) (.snd (v d))))) fun req =>
  .iteC (natEq (v bud) (.litNat 0)) (.ret (.pair aNone (.pair (.litNat 0) (v core)))) <|
  letV (.fst (v req)) fun spkSk => letV (.fst (.snd (v req))) fun spkPk =>
  letV (.fst (.snd (.snd (v req)))) fun u => letV (.fst (.snd (.snd (.snd (v req))))) fun j =>
  letV (.snd (.snd (.snd (.snd (v req))))) fun ikA =>
  bindV (Comp.queryChal (C := eufCmaSignOracle) (33 : ℕ+) (encEC (v spkPk))) fun sig1 =>
  bindV .sampleRandom64C fun seed =>
  bindV (Comp.queryPrimC (C := eufCmaSignOracle) .kemKeyGen (v seed)) fun kp =>
  bindV (Comp.queryChal (C := eufCmaSignOracle) (1569 : ℕ+) (encKEM (.fst (v kp)))) fun sig2 =>
  .ret (.pair
    (aBundle (buMk (v ikA) (.u32OfNat (v j)) (v spkPk) (v sig1) .noneE (.u32OfNat (v j))
      (.fst (v kp)) (v sig2)))
    (.pair (.sub (v bud) (.litNat 1)) (.pair (v fg) (.pair (v tp) (.pair (v tpk)
      (stUpd (v gs) (spks := .listCons (.pair (.pair (v u) (v j))
        (sbMk (v spkSk) (v spkPk) (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.litBool false)))
        (stSpks (v gs)))))))))

def sigInitDsl (S : Setup) : Comp pqxdhOps pqxdhEufCmaIface [B 32] (.prod .unit sigStTy) :=
  bindV (.sampleIndexC S.N_id) fun k => bindV .sampleBoolC fun b =>
  .ret (.pair .litUnit (.pair (.litNat S.N_spk_tot) (.pair .noneE (.pair (v k)
    (.pair (.var (.vs (.vs .vz)) : Expr pqxdhOps [.bool, .nat, B 32] (B 32)) (emptyAuthStE (v b)))))))

def sigFinishDsl (S : Setup) : Comp pqxdhOps pqxdhEufCmaIface [sigStTy, .bool] (.prod (B 1569) (B 64)) :=
  .ret (.ite (natEq (.litNat S.N_id) (.litNat 0)) (.pair (.litBytes 1569 []) (.litBytes 64 []))
    (eCaseOpt (.fst (.snd (.var .vz))) (.pair (.litBytes 1569 []) (.litBytes 64 [])) fun f => v f))

/-- `ReductionDsl` program for `sigReductionAuth` with list-traversal bound `K`. -/
def sigReductionAuthProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqxdhEufCmaIface (authSpec S) (authCodec S)
      (B 32) .unit .bool (.prod (B 1569) (B 64)) where
  σ      := sigStTy
  init   := sigInitDsl S
  handle := sigHandleDsl S K
  finish := sigFinishDsl S

def sigInit2Dsl (S : Setup) (K : Nat) :
    Comp pqxdhOps pqxdhEufCmaIface [B 32] (.prod .unit sigStTy) :=
  if S.N_id = 0 then
    .ret (.pair .litUnit (.pair (.litNat 0) (.pair .noneE (.pair (.litNat 0)
      (.pair (.var .vz : Expr pqxdhOps [B 32] (B 32)) (emptyAuthStE (.litBool false)))))))
  else
    bindV (.sampleIndexC S.N_id) fun k => bindV .sampleBoolC fun b =>
    .ret (.pair .litUnit (.pair (.litNat (min K S.N_spk_tot)) (.pair .noneE (.pair (v k)
      (.pair (.var (.vs (.vs .vz)) : Expr pqxdhOps [.bool, .nat, B 32] (B 32))
        (emptyAuthStE (v b)))))))

def sigFinish2Dsl (S : Setup) :
    Comp pqxdhOps pqxdhEufCmaIface [sigStTy, .bool] (.prod (B 1569) (B 64)) :=
  if S.N_id = 0 then
    .ret (.pair (.litBytes 1569 []) (.litBytes 64 []))
  else
    .ret (eCaseOpt (.fst (.snd (.var .vz)))
      (.pair (.litBytes 1569 []) (.litBytes 64 [])) fun f => v f)

/-- Clamped `ReductionDsl` program for `sigReductionAuth` with `K`-bounded signing budget literal. -/
def sigReductionAuthProg2 (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqxdhEufCmaIface (authSpec S) (authCodec S)
      (B 32) .unit .bool (.prod (B 1569) (B 64)) where
  σ      := sigStTy
  init   := sigInit2Dsl S K
  handle := sigHandleDsl S K
  finish := sigFinish2Dsl S

end SignalPqxdh.Security.ReductionDsl.AuthHs
