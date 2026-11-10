/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeGapDh
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyInd1KeyGapDh
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyGapDhIdSim

/-!
# One-Key `Auth` `GapDhWithSign` `ReductionDsl` Program

**Checked by Lean.** Defines the `ReductionDsl` program `fgAuth1KeyGapDhProg` for the one-key
`Auth` `GapDhWithSign` simulator `fgAuth1KeyGapDhAdv4` over `pqSigAndDdhIface`, together with its
context-generic step `a1gStepC` and tuple-keyed variant `a1gStep2C`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthHs

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh SignalPqxdh.LegacyCosted SignalPqxdh.Security SignalPqxdh.Security.ReductionDsl
open OracleSpec OracleComp

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] sigAndDdhOracle
end

abbrev CS := Comp pqxdhOps pqSigAndDdhIface

abbrev a1gStTy : Ty pqSig := .prod gsTy .nat

abbrev RSB : Ty pqSig := .prod authRespTy (.prod fgSimTy .nat)

/-- Tuple-keyed target role: `.inl u` (`DH1`), `.inr (.inl (u, i))` (`sendOPK`), or
    `.inr (.inr (u, i))` (`sendNoOPK`). -/
abbrev a1gRole2Ty : Ty pqSig :=
  .sum .nat (.sum (.prod .nat .nat) (.prod .nat .nat))

abbrev a1gParams2Ty : Ty pqSig :=
  .prod (B 32) (.prod (B 32) (.prod a1gRole2Ty (.opt (.prod .nat .nat))))

abbrev gs2Ty : Ty pqSig := .prod a1gParams2Ty fgSimTy

abbrev a1g2StTy : Ty pqSig := .prod gs2Ty .nat

@[reducible] def pa2U {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1gParams2Ty) :
    Expr pqxdhOps Γ (B 32) := .fst e
@[reducible] def pa2V {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1gParams2Ty) :
    Expr pqxdhOps Γ (B 32) := .fst (.snd e)
@[reducible] def pa2Role {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1gParams2Ty) :
    Expr pqxdhOps Γ a1gRole2Ty := .fst (.snd (.snd e))
@[reducible] def pa2TS {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1gParams2Ty) :
    Expr pqxdhOps Γ (.opt (.prod .nat .nat)) := .snd (.snd (.snd e))
@[reducible] def pa2Dh1 {Γ : List (Ty pqSig)} (e : Expr pqxdhOps Γ a1gParams2Ty) :
    Expr pqxdhOps Γ .bool :=
  eCaseSum (pa2Role e) (fun _ => .litBool true) (fun _ => .litBool false)

/-- Exact `Bernoulli(A / (A + B))` sampler over `pqGapDhIface` with constant AST size. -/
def bernoulliRatioC {Δ : List (Ty pqSig)} (A B : Nat) : CG Δ .bool :=
  if A = 0 then
    .ret (.litBool false)
  else if B = 0 then
    .ret (.litBool true)
  else if A ≤ B then
    bindV (.sampleIndexC (A + B)) fun x =>
    bindV (.sampleIndexC A) fun y1 =>
    bindV (.sampleIndexC A) fun y2 =>
    .ret (.lt (v x) (.add (.add (v y1) (v y2)) (.litNat 1)))
  else
    bindV (.sampleIndexC (A + B)) fun x =>
    bindV (.sampleIndexC B) fun y1 =>
    bindV (.sampleIndexC B) fun y2 =>
    .ret (.boolNot (.lt (v x) (.add (.add (v y1) (v y2)) (.litNat 1))))

section Branches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def a1gInitPrinC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (.pair aNone (v sim))) <|
  letV (.boolAnd (paDh1 (v pa)) (natEq (v u) (paTI (v pa)))) fun isT =>
  bindV .sampleBytes32C fun s0 => bindV (.queryPrimC .x25519Base (v s0)) fun pk0 =>
  letV (.ite (v isT) (.litBytes 32 []) (v s0)) fun sec0 =>
  letV (.ite (v isT) (paU (v pa)) (v pk0)) fun ikPk =>
  .ret (.pair (aInitPrin (v ikPk) (v ikPk))
    (fsUpd (v sim)
      (base := stUpd (v st) (prin := .listCons
        (.pair (v u) (peMk (v sec0) (v ikPk) (v sec0) (v ikPk) (.litBool false)))
        (stPrin (v st))))))

def a1gGenSpkC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (x : Var Γ₄ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : CS Δ RSB :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x))
    (.ret (.pair aNone (.pair (v sim) (v sigB)))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (.pair (v sim) (v sigB)))) fun uE =>
  .iteC (natEq (v sigB) (.litNat 0)) (.ret (.pair aNone (.pair (v sim) (v sigB)))) <|
  letV (natEq (.add (.mulK (nRecvEff S) (.fst (v x))) (.snd (v x))) (paTS (v pa))) fun isT =>
  bindV .sampleBytes32C fun skRaw =>
  bindV (.queryPrimC .x25519Base (v skRaw)) fun pkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v skRaw)) fun spkSk =>
  letV (.ite (v isT) (paV (v pa)) (v pkRaw)) fun spkPk =>
  bindV (KeyInd1KeyGapDh.sigChalQ_dsl 33 (encEC (v spkPk))) fun sig1 =>
  bindV .sampleRandom64C fun seed =>
  bindV (.queryPrimC .kemKeyGen (v seed)) fun kp =>
  bindV (KeyInd1KeyGapDh.sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun sig2 =>
  .ret (.pair (aBundle (buMk (peIkAPk (.snd (v uE))) (.u32OfNat (.snd (v x))) (v spkPk)
      (v sig1) .noneE (.u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (.pair
      (fsUpd (v sim) (base := stUpd (v st) (spks := .listCons (.pair (v x) (sbMk (v spkSk)
        (v spkPk) (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.litBool false)))
        (stSpks (v st)))))
      (.sub (v sigB) (.litNat 1))))

def a1gPreC (pa : Var Γ₁ paramsTy) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (q : Var Γ₄ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    CS Δ (.sum RSB .unit) :=
  caseSumV (v q)
    (fun u => bindV (KeyInd1KeyGapDh.liftGdhComp (a1gInitPrinC K pa sim u)) fun r =>
      .ret (.inl (.pair (.fst (v r)) (.pair (.snd (v r)) (v sigB))))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q)
    (fun x => .iteC (.boolAnd (paDh1 (v pa)) (natEq (.fst (v x)) (paTI (v pa))))
      (bindV (a1gGenSpkC S K pa sim sigB x) fun r => .ret (.inl (v r)))
      (.ret (.inr .unit))) fun _ =>
  .ret (.inr .unit)

/-- Context-generic one-key per-query step `fgAuth1KeyStepHalt`. -/
def a1gStepC (st : Var Γ₁ a1gStTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ (.prod authRespTy a1gStTy) :=
  letV (.fst (.fst (v st))) fun pa =>
  letV (.snd (.fst (v st))) fun sim =>
  letV (.snd (v st)) fun sigB =>
  .iteC (.boolAnd (paDh1 (v pa))
      (eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (paTI (v pa)))
        (.litBool false) fun e => peCorrupted (.snd (v e))))
    (.ret (.pair aNone (v st))) <|
  bindV (a1gPreC S K pa sim sigB q) fun pre =>
  caseSumV (v pre)
    (fun r => .ret (.pair (.fst (v r))
      (.pair (.pair (v pa) (.fst (.snd (v r)))) (.snd (.snd (v r)))))) fun _ =>
  bindV (KeyInd1KeyGapDh.liftGdhComp (fgStepC S K pa sim q)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (.pair (v pa) (.snd (v r))) (v sigB)))

end Branches

def a1gHandleDsl (S : Setup) (K : Nat) :
    CS [a1gStTy, authQueryTy] (.prod authRespTy a1gStTy) :=
  a1gStepC S K (.vz : Var [a1gStTy, authQueryTy] a1gStTy)
    (.vs .vz : Var [a1gStTy, authQueryTy] authQueryTy)

def a1gInitDsl (S : Setup) : CS [.prod (B 32) (B 32)] (.prod .unit a1gStTy) :=
  bindV (KeyInd1KeyGapDh.liftGdhComp (fgInitDsl S)) fun r =>
  .ret (.pair .unit (.pair (.snd (v r)) (.litNat (min S.N_spk_tot S.N_recv))))

def a1gFinishDsl (S : Setup) (K : Nat) : CS [a1gStTy, .bool] (B 32) :=
  letV (.fst (.var .vz) : Expr pqxdhOps [a1gStTy, .bool] gsTy) fun gst =>
  KeyInd1KeyGapDh.renameComp (KeyInd1KeyGapDh.twoVarRen gst (.vs (.vs .vz)))
    (KeyInd1KeyGapDh.liftGdhComp (fgFinishDsl S K))

/-! ## Tuple-keyed program -/

section TupleBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}

def fgInitPrin2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (.pair aNone (v sim))) <|
  letV (eCaseSum (pa2Role (v pa)) (fun uT => natEq (v u) (v uT)) (fun _ => .litBool false)) fun isT =>
  bindV .sampleBytes32C fun s0 => bindV (.queryPrimC .x25519Base (v s0)) fun ik =>
  bindV .sampleBytes32C fun s1 => bindV (.queryPrimC .sigPkGen (v s1)) fun sp =>
  letV (peMk (.ite (v isT) (.litBytes 32 []) (v s0)) (.ite (v isT) (pa2U (v pa)) (v ik))
      (v s1) (v sp) (.litBool false)) fun ent =>
  .ret (.pair (aInitPrin (peIkAPk (v ent)) (v sp))
    (fsUpd (v sim)
      (base := stUpd (v st) (prin := .listCons (.pair (v u) (v ent)) (stPrin (v st))))))

def fgGenSpk2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ (.prod .nat .nat))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x)) (.ret (.pair aNone (v sim))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v sim))) fun uE =>
  letV (eCaseOpt (pa2TS (v pa)) (.litBool false) fun bPair => nat2Eq (v x) (v bPair)) fun isT =>
  bindV .sampleBytes32C fun skRaw =>
  bindV (.queryPrimC .x25519Base (v skRaw)) fun pkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v skRaw)) fun spkSk =>
  letV (.ite (v isT) (pa2V (v pa)) (v pkRaw)) fun spkPk =>
  bindV .sampleRandom64C fun r1 =>
  bindV (.queryPrimC (.sigSign 33)
      (.pair (peSecIKAsign (.snd (v uE))) (.pair (encEC (v spkPk)) (v r1))))
    fun sig1 =>
  bindV .sampleRandom64C fun seed =>
  bindV (.queryPrimC .kemKeyGen (v seed)) fun kp =>
  bindV .sampleRandom64C fun r2 =>
  bindV (.queryPrimC (.sigSign 1569) (.pair (peSecIKAsign (.snd (v uE)))
    (.pair (encKEM (.fst (v kp))) (v r2)))) fun sig2 =>
  .ret (.pair (aBundle (buMk (peIkAPk (.snd (v uE))) (.u32OfNat (.snd (v x))) (v spkPk)
      (v sig1) .noneE (.u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (fsUpd (v sim) (base := stUpd (v st) (spks := .listCons (.pair (v x) (sbMk (v spkSk) (v spkPk)
      (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.litBool false))) (stSpks (v st))))))

def fgSend2C (opk : Bool) (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (x : Var Γ₃ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  .iteC (sendGuardE opk (v x)) (.ret (.pair aNone (v sim))) <|
  letV (fsBase (v sim)) fun st => letV (fsPows (v sim)) fun pows =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .iteC (.boolNot (natEq (.bytesLen (v m0)) (.bytesLen (v m1)))) (.ret (.pair aNone (v sim))) <|
  .iteC (eAny K (stUsedS (v st)) fun e => sidEq (v e) (v sid)) (.ret (.pair aNone (v sim))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (v sim))) fun uE =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (findHonestC S K st (buIkB (v bu)))) fun pp =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  .iteC (.boolAnd (.boolNot (v fresh)) (.boolNot (.bytesBeq (v m0) (v m1))))
    (.ret (.pair aNone (v sim))) <|
  bindV (Comp.liftChal (C := gapDhDdhOracle) (koskBundleOkPowsC S K st pows bu)) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (v sim))) <|
  letV (eCaseSum (pa2Role (v pa)) (fun _ => .litBool false) fun s =>
      eCaseSum (v s)
        (fun p => if opk then nat2Eq (.pair (.fst (v x)) (.fst (.snd (v x)))) (v p) else .litBool false)
        (fun p => if opk then .litBool false else nat2Eq (.pair (.fst (v x)) (.fst (.snd (v x)))) (v p)))
    fun isT =>
  bindV .sampleBytes32C fun ekRaw =>
  bindV .sampleBytes32C fun coins =>
  bindV .sampleBytes32C fun ephSk =>
  bindV .sampleBytes32C fun spqrCoins =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (resolveSigPkC S K st (buIkB (v bu)))) fun spk =>
  bindV (.queryPrimC (.sigVerify 33)
      (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu)))))
    fun v1 =>
  bindV (.queryPrimC (.sigVerify 1569)
      (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu)))))
    fun v2 =>
  .iteC (.boolNot (.boolAnd (v v1) (v v2))) (.ret (.pair aNone (v sim))) <|
  bindV (.queryPrimC .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc) (.ret (.pair aNone (v sim))) fun sc =>
  bindV (.queryPrimC .x25519Base (v ekRaw)) fun ekPkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v ekRaw)) fun ekSk =>
  letV (.ite (v isT) (pa2U (v pa)) (v ekPkRaw)) fun ekPk =>
  bindV (Comp.liftChal (C := gapDhDdhOracle) (lookupSpkSkC S K st pows (buSpkB (v bu)))) fun spkSk =>
  bindV (twoSideC (q4 (peSecIKA0 (.snd (v uE))) (v spkSk)
      (peIkAPk (.snd (v uE))) (buSpkB (v bu))))
    fun p1 =>
  bindV (twoSideC (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (buIkB (v bu)))) fun p2 =>
  bindV (twoSideC (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (buSpkB (v bu)))) fun p3 =>
  bindV (twoSideOptC (eCaseOpt (buOpkB (v bu)) .noneE fun o =>
      .someE (q4 (v ekSk) (.litBytes 32 []) (v ekPk) (.snd (v o))))) fun p4 =>
  letV (.pair (v p1) (.pair (v p2) (.pair (v p3) (.pair (v p4) (.fst (v sc)))))) fun pk =>
  bindV (patchC K pk (fsL (v sim))) fun dr =>
  bindV (.queryPrimC .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrimC .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (mkSecretPosC (v dhR)) fun posR =>
  bindV (rootPatchC K (.fst (.fst (v dr))) (v posR) (fsRootL (v sim))) fun rkOut =>
  bindV (.queryPrimC .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrimC .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrimC (.spqrInitSend 32 32)
      (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins))) fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone (v sim))) fun sp =>
  bindV (.queryPrimC (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (.snd (v uE))) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp))))
    fun ad =>
  bindV (.queryPrimC (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad)
      (.ite (v fresh) (.ite (stSecb (v st)) (v m1) (v m0)) (v m0))))) fun ct =>
  letV (.pair (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) (.pair (v ephPk) (.pair (.snd (.snd (v sp))) (v ct))))
    fun wm =>
  letV (eCaseOpt (v pp) (.pair (.litBool false) (.litBool false)) fun p =>
      .pair (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))
        (eAny K (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))) fun hon =>
  letV (seMk (v sid) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu))) (buPqspkB (v bu))
      (.fst (v hon)) (.litBool false) (.snd (v hon)) (v ekSk) (v ephSk) (v fresh)
      (.boolAnd (v fresh) (.boolNot (.bytesBeq (v m0) (v m1))))) fun se =>
  .ret (.pair (eCaseOpt (v pp)
      (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (fsUpd (v sim) (base := stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
        (usedS := .listCons (v sid) (stUsedS (v st))))
      (fgL := .snd (v dr)) (rootL := .snd (v rkOut))))

def fgStep2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (q : Var Γ₃ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  caseSumV (v q) (fun u => fgInitPrin2C K pa sim u) fun q =>
  caseSumV (v q) (fun u => onBaseF sim fun g => corruptB K g u) fun q =>
  caseSumV (v q) (fun x => fgGenSpk2C K pa sim x) fun q =>
  caseSumV (v q) (fun x => onBaseF sim fun g => genOpkB K g x) fun q =>
  caseSumV (v q) (fun x => fgSend2C S K true pa sim x) fun q =>
  caseSumV (v q) (fun x => fgSend2C S K false pa sim x) fun q =>
  caseSumV (v q) (fun x => fgRecvB S K true sim x) fun q =>
  caseSumV (v q) (fun x => fgRecvB S K false sim x) fun q =>
  caseSumV (v q) (fun sec => fgRoC K sim sec) fun q =>
  caseSumV (v q) (fun x => fgRoRootC K sim x) fun q =>
  caseSumV (v q) (fun _ => .ret (.pair aNone (v sim))) fun sk =>
  fgRegisterC sim sk

def a1gInitPrin2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (u : Var Γ₃ .nat)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ RSF :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stPrin (v st)) fun e => natEq (.fst (v e)) (v u)) (.ret (.pair aNone (v sim))) <|
  letV (eCaseSum (pa2Role (v pa)) (fun uT => natEq (v u) (v uT)) (fun _ => .litBool false)) fun isT =>
  bindV .sampleBytes32C fun s0 => bindV (.queryPrimC .x25519Base (v s0)) fun pk0 =>
  letV (.ite (v isT) (.litBytes 32 []) (v s0)) fun sec0 =>
  letV (.ite (v isT) (pa2U (v pa)) (v pk0)) fun ikPk =>
  .ret (.pair (aInitPrin (v ikPk) (v ikPk))
    (fsUpd (v sim)
      (base := stUpd (v st) (prin := .listCons
        (.pair (v u) (peMk (v sec0) (v ikPk) (v sec0) (v ikPk) (.litBool false)))
        (stPrin (v st))))))

def a1gGenSpk2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (x : Var Γ₄ (.prod .nat .nat)) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : CS Δ RSB :=
  letV (fsBase (v sim)) fun st =>
  .iteC (eAny K (stSpks (v st)) fun e => nat2Eq (.fst (v e)) (v x))
    (.ret (.pair aNone (.pair (v sim) (v sigB)))) <|
  caseOptV (eFind K (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (.pair aNone (.pair (v sim) (v sigB)))) fun uE =>
  .iteC (natEq (v sigB) (.litNat 0)) (.ret (.pair aNone (.pair (v sim) (v sigB)))) <|
  letV (eCaseOpt (pa2TS (v pa)) (.litBool false) fun bPair => nat2Eq (v x) (v bPair)) fun isT =>
  bindV .sampleBytes32C fun skRaw =>
  bindV (.queryPrimC .x25519Base (v skRaw)) fun pkRaw =>
  letV (.ite (v isT) (.litBytes 32 []) (v skRaw)) fun spkSk =>
  letV (.ite (v isT) (pa2V (v pa)) (v pkRaw)) fun spkPk =>
  bindV (KeyInd1KeyGapDh.sigChalQ_dsl 33 (encEC (v spkPk))) fun sig1 =>
  bindV .sampleRandom64C fun seed =>
  bindV (.queryPrimC .kemKeyGen (v seed)) fun kp =>
  bindV (KeyInd1KeyGapDh.sigChalQ_dsl 1569 (encKEM (.fst (v kp)))) fun sig2 =>
  .ret (.pair (aBundle (buMk (peIkAPk (.snd (v uE))) (.u32OfNat (.snd (v x))) (v spkPk)
      (v sig1) .noneE (.u32OfNat (.snd (v x))) (.fst (v kp)) (v sig2)))
    (.pair
      (fsUpd (v sim) (base := stUpd (v st) (spks := .listCons (.pair (v x) (sbMk (v spkSk)
        (v spkPk) (v sig1) (.snd (v kp)) (.fst (v kp)) (v sig2) (.litBool false)))
        (stSpks (v st)))))
      (.sub (v sigB) (.litNat 1))))

def a1gPre2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) (sigB : Var Γ₃ .nat)
    (q : Var Γ₄ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    CS Δ (.sum RSB .unit) :=
  caseSumV (v q)
    (fun u => bindV (KeyInd1KeyGapDh.liftGdhComp (a1gInitPrin2C K pa sim u)) fun r =>
      .ret (.inl (.pair (.fst (v r)) (.pair (.snd (v r)) (v sigB))))) fun q =>
  caseSumV (v q) (fun _ => .ret (.inr .unit)) fun q =>
  caseSumV (v q)
    (fun x => .iteC
      (eCaseSum (pa2Role (v pa)) (fun uT => natEq (.fst (v x)) (v uT)) (fun _ => .litBool false))
      (bindV (a1gGenSpk2C K pa sim sigB x) fun r => .ret (.inl (v r)))
      (.ret (.inr .unit))) fun _ =>
  .ret (.inr .unit)

/-- Context-generic tuple-keyed one-key per-query step. -/
def a1gStep2C (st : Var Γ₁ a1g2StTy) (q : Var Γ₂ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CS Δ (.prod authRespTy a1g2StTy) :=
  letV (.fst (.fst (v st))) fun pa =>
  letV (.snd (.fst (v st))) fun sim =>
  letV (.snd (v st)) fun sigB =>
  .iteC (eCaseSum (pa2Role (v pa))
      (fun uT =>
        eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (v uT))
          (.litBool false) fun e => peCorrupted (.snd (v e)))
      (fun _ => .litBool false))
    (.ret (.pair aNone (v st))) <|
  bindV (a1gPre2C K pa sim sigB q) fun pre =>
  caseSumV (v pre)
    (fun r => .ret (.pair (.fst (v r))
      (.pair (.pair (v pa) (.fst (.snd (v r)))) (.snd (.snd (v r)))))) fun _ =>
  bindV (KeyInd1KeyGapDh.liftGdhComp (fgStep2C S K pa sim q)) fun r =>
  .ret (.pair (.fst (v r)) (.pair (.pair (v pa) (.snd (v r))) (v sigB)))

def findMap2C {τ : Ty pqSig} (pa : Var Γ₁ a1gParams2Ty) [Ext Γ₁ Δ] (N : Nat)
    (xs : Expr pqxdhOps Δ (.list τ))
    (f : (x : Var (τ :: .opt (B 32) :: Δ) τ) → CG (τ :: .opt (B 32) :: Δ) (B 32)) :
    CG Δ (.opt (B 32)) :=
  foldMV N xs .noneE fun x acc =>
    caseOptV (v acc)
      (bindV (f x) fun z =>
        bindV (Comp.queryDdh (.pair (pa2U (v pa)) (.pair (pa2V (v pa)) (v z)))) fun b =>
        .ret (.ite (v b) (.someE (v z)) .noneE))
      fun _ => .ret (v acc)

def logScan2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] (off : Nat) :
    CG Δ (.opt (B 32)) :=
  findMV K (eMap K (fsLog (v sim)) fun s => slice32 off (v s)) fun z =>
    Comp.queryDdh (.pair (pa2U (v pa)) (.pair (pa2V (v pa)) (v z)))

def respCand2C (sim : Var Γ₁ fgSimTy) (r : Var Γ₂ respRecTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (pk : Expr pqxdhOps Δ (B 32)) : CG Δ (B 32) :=
  .queryPrimC .x25519 (.pair
    (eCaseOpt (eFind (min K S.N_dh) (stSpks (fsBase (v sim))) fun e => nat2Eq (.fst (v e)) (.fst (v r)))
      (.litBytes 32 []) fun e => sbSpkSk (.snd (v e)))
    pk)

def initDh1Cand2C (sim : Var Γ₁ fgSimTy) (spkPows : Var Γ₂ (.list (.prod (B 32) (B 32))))
    (s : Var Γ₃ authSessionEntryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : CG Δ (B 32) :=
  bindV (.queryPrimC .pow8 (sePeerSpk (v s))) fun w =>
  letV (eCaseOpt (eFind (min K S.N_dh) (v spkPows) fun e =>
        .boolAnd (.boolNot (bytesEmpty (.fst (v e)))) (.bytesBeq (.snd (v e)) (v w)))
      (eCaseOpt (eFind K (fsPows (v sim)) fun e => .bytesBeq (.snd (v e)) (v w))
        (.litBytes 32 []) fun e => .fst (v e))
      fun e => .fst (v e)) fun spkSk =>
  letV (eCaseSum (seSid (v s)) (fun p => .fst (v p)) fun r => eCaseSum (v r) (fun p => .fst (v p))
      fun r => eCaseSum (v r) (fun p => .fst (v p)) fun p => .fst (v p)) fun uIdx =>
  letV (eCaseOpt (eFind K (stPrin (fsBase (v sim))) fun e => natEq (.fst (v e)) (v uIdx))
      (.litBytes 32 []) fun e => peIkAPk (.snd (v e))) fun ikA =>
  .queryPrimC .x25519 (.pair (v spkSk) (v ikA))

def fgExtract2C (pa : Var Γ₁ a1gParams2Ty) (sim : Var Γ₂ fgSimTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] :
    CG Δ (B 32) :=
  .iteC (pa2Dh1 (v pa))
    (bindV (logScan2C K pa sim 32) fun f =>
     caseOptV (v f)
       (bindV (mapMV (min K S.N_dh) (stSpks (fsBase (v sim))) fun e =>
           bindV (.queryPrimC .pow8 (sbSpkPk (.snd (v e)))) fun w =>
           .ret (.pair (sbSpkSk (.snd (v e))) (v w))) fun spkPows =>
        bindV (findMap2C pa (min K S.N_dh) (stSess (fsBase (v sim)))
            fun s => initDh1Cand2C S K sim spkPows s)
          fun f2 =>
        caseOptV (v f2)
          (bindV (findMap2C pa (min K S.N_sess_tot) (fsResp (v sim)) fun r =>
              respCand2C S K sim r (.fst (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))
    (bindV (logScan2C K pa sim 96) fun f =>
     caseOptV (v f)
       (bindV (findMap2C pa (min K S.N_dh) (stSess (fsBase (v sim))) fun s =>
           .iteC (bytesEmpty (seEkASk (v s))) (.ret zero32)
             (.queryPrimC .x25519 (.pair (seEkASk (v s)) (sePeerSpk (v s))))) fun f2 =>
        caseOptV (v f2)
          (bindV (findMap2C pa (min K S.N_sess_tot) (fsResp (v sim)) fun r =>
              respCand2C S K sim r (.snd (.snd (v r)))) fun f3 =>
           .ret (eCaseOpt (v f3) zero32 fun z => v z))
          fun z => .ret (v z))
       fun z => .ret (v z))

end TupleBranches

def sampleSpkPair2C (S : Setup) {Δ : List (Ty pqSig)} : CG Δ (.opt (.prod .nat .nat)) :=
  if S.N_spk_tot = 0 then
    .ret .noneE
  else
    bindV (.sampleIndexC S.N_id) fun uS =>
    bindV (.sampleIndexC S.N_recv) fun jS =>
    .ret (.someE (.pair (v uS) (v jS)))

def sampleRole2C (S : Setup) {Δ : List (Ty pqSig)} : CG Δ a1gRole2Ty :=
  if S.N_id = 0 then
    .ret (.inr (.inl (.pair (.litNat 0) (.litNat 0))))
  else
    bindV (.sampleIndexC S.N_id) fun uT =>
    bindV (.sampleIndexC (1 + S.N_send_opk + S.N_send_no_opk)) fun w =>
    .iteC (natEq (v w) (.litNat 0))
      (.ret (.inl (v uT)))
      (if S.N_send_opk_tot = 0 then
         if S.N_send_no_opk_tot = 0 then
           .ret (.inr (.inl (.pair (.litNat 0) (.litNat 0))))
         else
           bindV (.sampleIndexC S.N_send_no_opk) fun iT =>
           .ret (.inr (.inr (.pair (v uT) (v iT))))
       else if S.N_send_no_opk_tot = 0 then
         bindV (.sampleIndexC S.N_send_opk) fun iT =>
         .ret (.inr (.inl (.pair (v uT) (v iT))))
       else
         bindV (bernoulliRatioC S.N_send_opk S.N_send_no_opk) fun useOpk =>
         .iteC (v useOpk)
           (bindV (.sampleIndexC S.N_send_opk) fun iT =>
            .ret (.inr (.inl (.pair (v uT) (v iT)))))
           (bindV (.sampleIndexC S.N_send_no_opk) fun iT =>
            .ret (.inr (.inr (.pair (v uT) (v iT))))))

def fgInit2Dsl (S : Setup) : CG [.prod (B 32) (B 32)] (.prod .unit gs2Ty) :=
  bindV (sampleRole2C S) fun role =>
  bindV (sampleSpkPair2C S) fun spk? =>
  bindV .sampleBoolC fun secb =>
  let uv : Expr pqxdhOps [.bool, .opt (.prod .nat .nat), a1gRole2Ty, .prod (B 32) (B 32)]
      (.prod (B 32) (B 32)) := .var (.vs (.vs (.vs .vz)))
  .ret (.pair .litUnit (.pair
    (.pair (.fst uv) (.pair (.snd uv) (.pair (v role) (v spk?))))
    (emptySimE (v secb))))

def fgFinish2Dsl (S : Setup) (K : Nat) : CG [gs2Ty, .bool] (B 32) :=
  letV (.fst (.var .vz) : Expr pqxdhOps [gs2Ty, .bool] a1gParams2Ty) fun pa =>
  letV (.snd (.var (.vs .vz)) : Expr pqxdhOps [a1gParams2Ty, gs2Ty, .bool] fgSimTy) fun sim =>
  fgExtract2C S K pa sim

def a1g2HandleDsl (S : Setup) (K : Nat) :
    CS [a1g2StTy, authQueryTy] (.prod authRespTy a1g2StTy) :=
  a1gStep2C S K (.vz : Var [a1g2StTy, authQueryTy] a1g2StTy)
    (.vs .vz : Var [a1g2StTy, authQueryTy] authQueryTy)

def a1g2InitDsl (S : Setup) (K : Nat) : CS [.prod (B 32) (B 32)] (.prod .unit a1g2StTy) :=
  bindV (KeyInd1KeyGapDh.liftGdhComp (fgInit2Dsl S)) fun r =>
  .ret (.pair .unit (.pair (.snd (v r)) (.litNat (min K (min S.N_spk_tot S.N_recv)))))

def a1g2FinishDsl (S : Setup) (K : Nat) : CS [a1g2StTy, .bool] (B 32) :=
  letV (.fst (.var .vz) : Expr pqxdhOps [a1g2StTy, .bool] gs2Ty) fun gst =>
  KeyInd1KeyGapDh.renameComp (KeyInd1KeyGapDh.twoVarRen gst (.vs (.vs .vz)))
    (KeyInd1KeyGapDh.liftGdhComp (fgFinish2Dsl S K))

/-- `ReductionDsl` program for `fgAuth1KeyGapDhAdv4 S b` at list capacity `K`. -/
def fgAuth1KeyGapDhProg (S : Setup) (K : Nat) :
    CostedReduction pqxdhOps pqSigAndDdhIface (authSpec S) (authCodec S)
      (.prod (B 32) (B 32)) .unit .bool (B 32) where
  σ      := a1g2StTy
  init   := a1g2InitDsl S K
  handle := a1g2HandleDsl S K
  finish := a1g2FinishDsl S K

abbrev fgAuth1KeyGapDhDslProg (S : Setup) (b : QueryBudget) :=
  fgAuth1KeyGapDhProg S b.q_total

end SignalPqxdh.Security.ReductionDsl.AuthHs
