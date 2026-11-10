/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfBase

/-!
# `ReductionDsl` Program for the `Auth` `AeadIndCpa` Reduction

Defines the two-stage `ReductionDsl` program `aeadCpaRedProg S K` mirroring the shallow
`aeadCpaReductionAuthFixed` reduction.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

/-! ## Types -/

abbrev provTy : PT := .prod .bool (.prod .bool .bool)

/-- DSL encoding of the `AuthCpaPausePayload` fields consumed by `finishAuthCpaSendFixedPure`. -/
abbrev cpaPayloadTy : PT :=
  .prod sessionIdTy (.prod principalEntryTy (.prod (.opt (.prod .nat principalEntryTy))
    (.prod preKeyBundleTy (.prod (.prod (B 32) (B 32))
      (.prod (.prod (B 32) (.prod (B 32) (.prod (B 32) (.prod (B 1568) (.prod (B 32) (B 32))))))
        (.prod drKeyTy (.prod (.prod (B 32) (.prod (B 32) (.prod (B 32) (B 32))))
          (.prod (.opt (B 32)) (.prod (B 32) (.prod (B 158) (.prod provTy
            (.prod (.list (.prod (B 192) drKeyTy))
              (.list (.prod (.prod (B 32) (B 32)) (.prod (B 32) (B 32))))))))))))))))

abbrev cpaChOutTy : PT := .prod (B 158) (.prod (B 32) (B 32))

abbrev cpaSlotStTy : PT := .prod .nat authHybridStateFixedTy

abbrev cpaStTy : PT := .prod .nat cpaSlotStTy

abbrev cpaSendResTy : PT :=
  .sum RSF (.prod cpaChOutTy (.prod cpaPayloadTy authHybridStateFixedTy))

abbrev cpaSlotSendResTy : PT :=
  .sum (.prod authRespTy cpaSlotStTy) (.prod cpaChOutTy (.prod cpaPayloadTy cpaSlotStTy))

abbrev cpaPreTy : PT :=
  .sum (.prod authRespTy cpaStTy) (.prod cpaChOutTy (.prod cpaPayloadTy cpaStTy))

def getDBytes {Γ : List PT} (o : Expr pqxdhOps Γ (.opt (B 32))) : Expr pqxdhOps Γ (B 32) :=
  eCaseOpt o (litB 32 []) fun x => v x

def defaultMsgKeysE {Γ : List PT} : Expr pqxdhOps Γ msgKeysTy :=
  .pair (litB 32 (default : MessageKeys).cipherKey)
    (.pair (litB 32 (default : MessageKeys).macKey) (litB 16 (default : MessageKeys).iv))

def iasAdE {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 158) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))))
def iasAeadCtE {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))))
def iasMsgPlainE {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd s)))))))))))))
def iasCk1_0E {Γ} (s : Expr pqxdhOps Γ idealAuthSessionTy) : Expr pqxdhOps Γ (B 32) :=
  .fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd s))))))))))))))))

section CpaBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Δ : List PT}

/-! ## Send -/

def finishCpaC (fhst : Var Γ₁ authHybridStateFixedTy) (fresh isIdeal : Expr pqxdhOps Δ .bool)
    (p : Expr pqxdhOps Δ cpaPayloadTy) (aeadCt : Expr pqxdhOps Δ (B 32)) [Ext Γ₁ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (.pair fresh (.pair isIdeal (.pair p aeadCt))) fun a =>
  letV (.fst (v a)) fun fresh =>
  letV (.fst (.snd (v a))) fun isIdeal =>
  letV (.fst (.snd (.snd (v a)))) fun p =>
  letV (.snd (.snd (.snd (v a)))) fun aeadCt =>
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (v p)) fun sid =>
  letV (.fst (.snd (v p))) fun uE =>
  letV (.fst (.snd (.snd (v p)))) fun pp =>
  letV (.fst (.snd (.snd (.snd (v p))))) fun bu =>
  letV (.fst (.snd (.snd (.snd (.snd (v p)))))) fun m01 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v p))))))) fun keys6 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (v p)))))))) fun drKey =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v p))))))))) fun rks4 =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v p)))))))))) fun spqrSalt? =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v p))))))))))) fun pqMsg =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (.snd (v p)))))))))))) fun ad =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (v p))))))))))))) fun prov =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (v p)))))))))))))) fun roC =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (.snd
    (.snd (.snd (.snd (.snd (.snd (.snd (v p)))))))))))))) fun rootC =>
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
        (v spqrSalt?) (v pqMsg) (v ad) (v aeadCt) (litB 32 []) (v drKey)
        (v rk1) (v ck1_0) (v mkSeed) (v ck1_1) defaultMsgKeysE) (ahsIdealSessions (v hst)))
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

def spkHonIdealFromPeerC (st : Var Γ₁ authStateTy)
    (pp : Var Γ₂ (.opt (.prod .nat principalEntryTy)))
    (bu : Var Γ₃ preKeyBundleTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    Comp pqxdhOps pqPrimIface Δ .bool :=
  caseOptV (v pp) (.ret (.bool false)) fun p =>
  letV (.fst (v p)) fun k =>
  letV (.snd (v p)) fun pE =>
  anyMV (min K S.N_dh) (asSpkBundles (v st)) fun b =>
    bindV (queryPrim .pow8 (sbSpkPk (.snd (v b)))) fun p1 =>
    bindV (queryPrim .pow8 (pkbSpkB (v bu))) fun p2 =>
    .ret (.and (natEq (.fst (.fst (v b))) (v k))
      (boolOr
        (.and (peCorrupted (v pE)) (bytesBeq 32 (v p1) (v p2)))
        (bytesBeq 32 (sbSpkPk (.snd (v b))) (pkbSpkB (v bu)))))

def cpaSendB (opk allowPause : Bool) (idx : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (x : Var Γ₃ sendQTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] :
    Comp pqxdhOps pqPrimIface Δ cpaSendResTy :=
  letV (.inl (.pair aNone (v fhst)) : Expr pqxdhOps _ cpaSendResTy) fun noneDone =>
  .ite (sendGuardE opk (v x)) (.ret (v noneDone)) <|
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret (v noneDone)) <|
  .ite (eAny K (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)) (.ret (v noneDone)) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneDone)) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1))))
    (.ret (v noneDone)) <|
  bindV (koskBundleOkC S K st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneDone)) <|
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
  .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
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
  bindV (queryPrim .x25519 (.pair (v ekASk) (getDBytes (optSnd (pkbOpkB? (v bu)))))) fun dh4Raw =>
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
  caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
  letV (.fst (.snd (v sp))) fun spqrSalt? =>
  letV (.snd (.snd (v sp))) fun pqMsg =>
  letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
  letV (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v bu) (.pair (.pair (v m0) (v m1))
      (.pair (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ss) (.pair (v kemCt)
        (.pair (v ephASk) (v ephAPk))))))
      (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
        (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v ad) (.pair (v prov)
          (.pair (v roC') (v rootC')))))))))))))) fun pl =>
  letV (sessionSlotIndexE S (v sid)) fun sIdx =>
  .ite (v isFresh)
    (letV (.ite (natLt (v sIdx) (v idx)) (v m0) (v m1)) fun msgPlain =>
     (if allowPause then
        .ite (natEq (v sIdx) (v idx))
          (.ret (.inr (.pair (.pair (v ad) (.pair (v m0) (v m1))) (.pair (v pl) (v fhst)))))
      else id) <|
     bindV (samplePrim .msgKeys80) fun mks =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishCpaC fhst (.bool true) (.bool true) (v pl) (v aeadCt)) fun res =>
     .ret (.inl (v res)))
    (bindV (.ite (v isIdealSend) (samplePrim .msgKeys80)
        (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?)))) fun mks =>
     bindV (queryPrim (.aeadEnc 158 32 32) (.pair (v mks) (.pair (v ad) (v m0)))) fun aeadCt =>
     bindV (finishCpaC fhst (.bool false) (v isIdealSend) (v pl) (v aeadCt)) fun res =>
     .ret (.inl (v res)))

/-! ## Receive -/

def cpaRecvC (opk : Bool) (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.add (ahsfRecvCount (v fhst)) (.nat 1)) fun rc' =>
  letV (.pair aNone (ahsfUpd (v fhst) (rc := v rc')) : Expr pqxdhOps _ RSF) fun noneRc =>
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
    (.ret (v noneRc)) <|
  .ite (eAny K (if opk then asUsedRecvOPK (v st) else asUsedRecvNoOPK (v st))
      fun e => nat3Eq (v e) (v kjo))
    (.ret (v noneRc)) <|
  bindV (koskSenderOkC S K st (hdrIkAPk (v hdr))) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneRc)) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneRc)) fun kPair =>
  caseOptV (eFind K (asSpkBundles (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (v noneRc)) fun bPair =>
  letV (.snd (v kPair)) fun kE =>
  letV (.snd (v bPair)) fun bE =>
  bindV (if opk then
      caseOptV (eFind K (asOpkEntries (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
        (.ret (.inl .unit)) fun oPair =>
      .ite (oeConsumed (.snd (v oPair))) (.ret (.inl .unit))
        (.ret (.inr (.some (.snd (v oPair)))))
    else .ret (.inr .none) : Comp pqxdhOps pqPrimIface _ (.sum .unit (.opt opkEntryTy))) fun oRes =>
  caseSumV (v oRes) (fun _ => .ret (v noneRc)) fun oE? =>
  letV (kyberCheckE K (asUsedKyberTriples (v st)) (.pair (.fst (v x)) (.pair (hdrPqspkId (v hdr))
      (.pair (hdrSpkId (v hdr)) (hdrEkAPk (v hdr)))))) fun kc =>
  bindV (queryPrim .isCanonical (hdrEkAPk (v hdr))) fun can =>
  bindV (queryPrim .isCanonical (pkmEphAPk (v msg))) fun canE =>
  .ite (boolOr (boolOr (.not (.fst (v kc))) (.not (v can))) (.not (v canE)))
    (.ret (v noneRc)) <|
  bindV (queryPrim .kemDecaps (.pair (sbPqspkSk (v bE)) (hdrKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (v noneRc)) fun ss =>
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
  letV (eCaseOpt (v oE?) .none fun oE => .some (oeOpkPk (v oE))) fun opkBPk? =>
  letV (ahsfMkSaltCache (v fhst)) fun cache =>
  letV (ahsfRecvCount (v fhst)) fun rc =>
  bindV (findHonestC S K st (hdrIkAPk (v hdr))) fun snd? =>
  letV (eCaseOpt (v snd?) (.bool false) fun sP => .not (peCorrupted (.snd (v sP))))
    fun isUncorr =>
  letV (peIkAPk (v kE)) fun ikBPk =>
  letV (sbSpkPk (v bE)) fun spkBPk =>
  letV (sbPqspkPk (v bE)) fun pqspkBPk =>
  bindV (findMV (min K S.N_sess_tot) (ahsIdealSessions (v hstDec)) fun s =>
      matchIdealAuthHandshakeC ikBPk spkBPk opkBPk? pqspkBPk hdr s) fun matched? =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .drKey96) fun dk => .ret (.pair (v dk) (asRoCache (v st))))
        (hkdfRoC K st (v secrets)))
      fun s => .ret (.pair (iasDrKey (v s)) (asRoCache (v st)))) fun drOut =>
  letV (.fst (v drOut)) fun drKey =>
  letV (.snd (v drOut)) fun roC' =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pkmEphAPk (v msg)))) fun dhR =>
  bindV (caseOptV (v matched?) (.ret (.bool false)) fun s =>
      bindV (queryPrim .pow8 (pkmEphAPk (v msg))) fun p1 =>
      bindV (queryPrim .pow8 (iasEphAPk (v s))) fun p2 =>
      .ret (bytesBeq 32 (v p1) (v p2))) fun sameEph =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
          .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))
        (rootRoC K st (.fst (v drKey)) (v dhR)))
      fun s => .ite (v sameEph)
        (.ret (.pair (.pair (iasRk1 (v s)) (iasCk1_0E (v s))) (asRootRoCache (v st))))
        (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
          .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))) fun rkOut =>
  letV (.fst (.fst (v rkOut))) fun rk1 =>
  letV (.snd (.fst (v rkOut))) fun ck1_0 =>
  letV (.snd (v rkOut)) fun rootC' =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
          .ret (.pair (v ms) (v cn)))
        (bindV (queryPrim .chainKdfSeed (v ck1_0)) fun ms =>
         bindV (queryPrim .chainKdfNext (v ck1_0)) fun cn => .ret (.pair (v ms) (v cn))))
      fun s => .ite (v sameEph)
        (.ret (.pair (iasMkSeed (v s)) (iasCk1_1 (v s))))
        (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
          .ret (.pair (v ms) (v cn))))
    fun mkc =>
  letV (.fst (v mkc)) fun mkSeed =>
  letV (.snd (v mkc)) fun ck1_1 =>
  bindV (queryPrim (.spqrInitRecv 32 32)
      (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
  letV (ahsUpd (v hstDec)) fun hstDecV =>
  caseOptV (v sp?)
    (.ret (.pair aNone (ahsfMk (v hstDecV) (v rc') (v cache)))) fun sp =>
  letV (.snd (v sp)) fun spqrSalt? =>
  letV (eCaseOpt (v matched?) (.bool false) fun s =>
      .and (v sameEph) (sameSaltKeyE (v spqrSalt?) (iasSpqrSalt? (v s)))) fun sameMk =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .msgKeys80) fun mk => .ret (.pair (v mk) (v cache)))
        (bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mk =>
          .ret (.pair (v mk) (v cache))))
      fun s => .ite (v sameMk) (.ret (.pair (iasMsgKeys (v s)) (v cache)))
        (.ite (v sameEph)
          (letV (.pair (iasSid (v s)) (v spqrSalt?)) fun cKey =>
           caseOptV (eFind K (v cache) fun e =>
               .and (sidEq (.fst (.fst (v e))) (iasSid (v s)))
                 (sameSaltKeyE (.snd (.fst (v e))) (v spqrSalt?)))
             (bindV (samplePrim .msgKeys80) fun mk =>
               .ret (.pair (v mk) (.cons (.pair (v cKey) (.pair (v rc) (v mk))) (v cache))))
             fun e => .ret (.pair (.snd (.snd (v e))) (v cache)))
          (bindV (samplePrim .msgKeys80) fun mk => .ret (.pair (v mk) (v cache))))) fun mkOut =>
  letV (.fst (v mkOut)) fun mks =>
  letV (.snd (v mkOut)) fun cache' =>
  letV (firstMsgADE (hdrIkAPk (v hdr)) (peIkAPk (v kE)) (pkmEphAPk (v msg))
      (pkmPqRatchetMsg (v msg))) fun ad =>
  letV (.pair aNone (ahsfMk (v hstDecV) (v rc') (v cache')) : Expr pqxdhOps _ RSF) fun noneDec =>
  bindV (.ite (v sameMk)
      (.ret (eCaseOpt (v matched?) .none fun s =>
        .ite (.and (bytesBeq 158 (v ad) (iasAdE (v s)))
            (bytesBeq 32 (pkmAeadCt (v msg)) (iasAeadCtE (v s))))
          (.some (iasMsgPlainE (v s))) .none))
      (.ite (v isUncorr) (.ret .none)
        (queryPrim (.aeadDec 158 32 32)
          (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))))) fun pt? =>
  caseOptV (v pt?) (.ret (v noneDec)) fun pt =>
  bindV (findHonestC S K st (hdrIkAPk (v hdr))) fun snd2? =>
  letV (eCaseOpt (v snd2?) (aRecvUnfresh (v drKey) (v rk1) (v ck1_1) (v pt)) fun _ => aRecvHonest)
    fun resp =>
  letV (ahsBase (v hstDec)) fun stD =>
  letV (if opk then
      stUpd (v stD)
        (opks := eMap K (asOpkEntries (v st)) fun e =>
          .ite (nat3Eq (.fst (v e)) (v kjo))
            (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .bool true))) (v e))
        (usedO := .cons (v kjo) (asUsedRecvOPK (v st)))
        (kyb := .snd (v kc)) (ro := v roC') (root := v rootC')
    else
      stUpd (v stD)
        (usedN := .cons (v kjo) (asUsedRecvNoOPK (v st)))
        (kyb := .snd (v kc)) (ro := v roC') (root := v rootC')) fun base' =>
  .ret (.pair (v resp) (ahsfMk (ahsUpd (v hstDec) (base := v base')) (v rc') (v cache')))

/-! ## Step dispatch -/

def wrapCpa (idx : Var Γ₁ .nat) [Ext Γ₁ Δ] (m : Comp pqxdhOps pqPrimIface Δ RSF) :
    Comp pqxdhOps pqPrimIface Δ (.prod authRespTy cpaStTy) :=
  bindV m fun r => .ret (.pair (.fst (v r)) (.pair (v idx) (.pair (.nat 0) (.snd (v r)))))

def cpaNonSendC (idx : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (q : Var Γ₃ authQueryTy) [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ]
    (send : (opk : Bool) → {Δ' : List PT} → [Ext Γ₁ Δ'] → [Ext Γ₂ Δ'] →
      Var Δ' sendQTy → Comp pqxdhOps pqPrimIface Δ' cpaPreTy)
    (inl : {Δ' : List PT} → [Ext Γ₁ Δ'] → Comp pqxdhOps pqPrimIface Δ' (.prod authRespTy cpaStTy) →
      Comp pqxdhOps pqPrimIface Δ' cpaPreTy) : Comp pqxdhOps pqPrimIface Δ cpaPreTy :=
  caseSumV (v q) (fun u => inl (wrapCpa idx (initPrinFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun u => inl (wrapCpa idx (corruptFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (genSpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (genOpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => send true x) fun q =>
  caseSumV (v q) (fun x => send false x) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (cpaRecvC S K true fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (cpaRecvC S K false fhst x))) fun q =>
  caseSumV (v q) (fun sec => inl (wrapCpa idx (roFixedB K fhst sec))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpa idx (roRootFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun _ => inl (.ret (.pair aNone (.pair (v idx) (.pair (.nat 0) (v fhst)))))) fun sk =>
  inl (wrapCpa idx (registerFixedB fhst sk))

end CpaBranches

section CpaSlotBranches

variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT}

/-- Creation-order send handler using `ns` as the fresh-send slot counter. -/
def cpaSendSlotB (opk allowPause : Bool) (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ cpaSlotSendResTy :=
  letV (.inl (.pair aNone (.pair (v ns) (v fhst))) : Expr pqxdhOps _ cpaSlotSendResTy) fun noneDone =>
  .ite (sendGuardE opk (v x)) (.ret (v noneDone)) <|
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret (v noneDone)) <|
  .ite (eAny K (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)) (.ret (v noneDone)) <|
  caseOptV (eFind K (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneDone)) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1))))
    (.ret (v noneDone)) <|
  bindV (koskBundleOkC S K st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneDone)) <|
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
  .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
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
  bindV (queryPrim .x25519 (.pair (v ekASk) (getDBytes (optSnd (pkbOpkB? (v bu)))))) fun dh4Raw =>
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
  caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
  letV (.fst (.snd (v sp))) fun spqrSalt? =>
  letV (.snd (.snd (v sp))) fun pqMsg =>
  letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
  letV (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v bu) (.pair (.pair (v m0) (v m1))
      (.pair (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ss) (.pair (v kemCt)
        (.pair (v ephASk) (v ephAPk))))))
      (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
        (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v ad) (.pair (v prov)
          (.pair (v roC') (v rootC')))))))))))))) fun pl =>
  .ite (v isFresh)
    (letV (.ite (natLt (v ns) (v idx)) (v m0) (v m1)) fun msgPlain =>
     (if allowPause then
        .ite (natEq (v ns) (v idx))
          (.ret (.inr (.pair (.pair (v ad) (.pair (v m0) (v m1)))
            (.pair (v pl) (.pair (v ns) (v fhst))))))
      else id) <|
     bindV (samplePrim .msgKeys80) fun mks =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishCpaC fhst (.bool true) (.bool true) (v pl) (v aeadCt)) fun res =>
     .ret (.inl (.pair (.fst (v res)) (.pair (.add (v ns) (.nat 1)) (.snd (v res))))))
    (bindV (.ite (v isIdealSend) (samplePrim .msgKeys80)
        (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?)))) fun mks =>
     bindV (queryPrim (.aeadEnc 158 32 32) (.pair (v mks) (.pair (v ad) (v m0)))) fun aeadCt =>
     bindV (finishCpaC fhst (.bool false) (v isIdealSend) (v pl) (v aeadCt)) fun res =>
     .ret (.inl (.pair (.fst (v res)) (.pair (v ns) (.snd (v res))))))

def wrapCpaSlot (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat) [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (m : Comp pqxdhOps pqPrimIface Δ RSF) :
    Comp pqxdhOps pqPrimIface Δ (.prod authRespTy cpaStTy) :=
  bindV m fun r => .ret (.pair (.fst (v r)) (.pair (v idx) (.pair (v ns) (.snd (v r)))))

def cpaNonSendSlotC (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (q : Var Γ₄ authQueryTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
    (send : (opk : Bool) → {Δ' : List PT} → [Ext Γ₁ Δ'] → [Ext Γ₂ Δ'] → [Ext Γ₃ Δ'] →
      Var Δ' sendQTy → Comp pqxdhOps pqPrimIface Δ' cpaPreTy)
    (inl : {Δ' : List PT} → [Ext Γ₁ Δ'] → [Ext Γ₂ Δ'] →
      Comp pqxdhOps pqPrimIface Δ' (.prod authRespTy cpaStTy) →
      Comp pqxdhOps pqPrimIface Δ' cpaPreTy) : Comp pqxdhOps pqPrimIface Δ cpaPreTy :=
  caseSumV (v q) (fun u => inl (wrapCpaSlot idx ns (initPrinFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun u => inl (wrapCpaSlot idx ns (corruptFixedB K fhst u))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (genSpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (genOpkFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun x => send true x) fun q =>
  caseSumV (v q) (fun x => send false x) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (cpaRecvC S K true fhst x))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (cpaRecvC S K false fhst x))) fun q =>
  caseSumV (v q) (fun sec => inl (wrapCpaSlot idx ns (roFixedB K fhst sec))) fun q =>
  caseSumV (v q) (fun x => inl (wrapCpaSlot idx ns (roRootFixedB K fhst x))) fun q =>
  caseSumV (v q) (fun _ => inl (.ret (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst)))))) fun sk =>
  inl (wrapCpaSlot idx ns (registerFixedB fhst sk))

end CpaSlotBranches

/-! ## Program -/

section Prog

variable (S : Setup) (K : Nat)

def cpaStepC (allowPause : Bool) : Comp pqxdhOps pqPrimIface [cpaStTy, authQueryTy] cpaPreTy :=
  letV (.fst (.var .zero) : Expr pqxdhOps [cpaStTy, authQueryTy] .nat) fun idx =>
  letV (.fst (.snd (.var (.succ .zero))) :
      Expr pqxdhOps [.nat, cpaStTy, authQueryTy] .nat) fun ns =>
  letV (.snd (.snd (.var (.succ (.succ .zero)))) :
      Expr pqxdhOps [.nat, .nat, cpaStTy, authQueryTy] authHybridStateFixedTy) fun fhst =>
  cpaNonSendSlotC S K idx ns fhst
    (.succ (.succ (.succ (.succ .zero))) :
      Var [authHybridStateFixedTy, .nat, .nat, cpaStTy, authQueryTy] authQueryTy)
    (fun opk => fun x =>
      bindV (cpaSendSlotB S K opk allowPause idx ns fhst x) fun r =>
      caseSumV (v r)
        (fun d => .ret (.inl (.pair (.fst (v d)) (.pair (v idx) (.snd (v d))))))
        (fun p => if allowPause then
            .ret (.inr (.pair (.fst (v p)) (.pair (.fst (.snd (v p)))
              (.pair (v idx) (.snd (.snd (v p)))))))
          else .ret (.inl (.pair aNone (.pair (v idx) (.pair (v ns) (v fhst)))))))
    (fun m => bindV m fun r => .ret (.inl (v r)))

def cpaPreC : Comp pqxdhOps pqPrimIface [cpaStTy, authQueryTy] cpaPreTy := cpaStepC S K true

def cpaPostC : Comp pqxdhOps pqPrimIface [cpaStTy, authQueryTy] (.prod authRespTy cpaStTy) :=
  bindV (cpaStepC S K false) fun r =>
  caseSumV (v r) (fun d => .ret (v d)) fun _ =>
    .ret (.pair aNone (.var (.succ (.succ .zero)) : Expr pqxdhOps _ cpaStTy))

def cpaInitC : Comp pqxdhOps pqPrimIface [.unit] (.prod .unit cpaStTy) :=
  bindV (samplePrim (.index (min K S.N_send_tot))) fun idx =>
  .ret (.pair .unit (.pair (v idx) (.pair (.nat 0) (emptyAuthHybridStFixedE (.bool true)))))

def cpaDefaultChC : Comp pqxdhOps pqPrimIface [cpaStTy, .bool] cpaChOutTy :=
  .ret (.pair (litB 158 []) (.pair (litB 32 [0]) (litB 32 [0])))

def cpaResumeC :
    Comp pqxdhOps pqPrimIface [cpaStTy, cpaPayloadTy, .opt (B 32)] (.prod authRespTy cpaStTy) :=
  letV (.fst (.var .zero) : Expr pqxdhOps [cpaStTy, cpaPayloadTy, .opt (B 32)] .nat) fun idx =>
  letV (.snd (.snd (.var (.succ .zero))) :
      Expr pqxdhOps [.nat, cpaStTy, cpaPayloadTy, .opt (B 32)] authHybridStateFixedTy) fun fhst =>
  bindV (finishCpaC fhst (.bool true) (.bool true)
      (.var (.succ (.succ (.succ .zero))) :
        Expr pqxdhOps [authHybridStateFixedTy, .nat, cpaStTy, cpaPayloadTy, .opt (B 32)] cpaPayloadTy)
      (getDBytes (.var (.succ (.succ (.succ (.succ .zero)))))))
    fun r => .ret (.pair (.fst (v r)) (.pair (v idx) (.pair (.add (v idx) (.nat 1)) (.snd (v r)))))

def cpaFinishC : Comp pqxdhOps pqPrimIface [cpaStTy, .bool, .opt (B 32)] .bool :=
  letV (.bool true : Expr pqxdhOps [cpaStTy, .bool, .opt (B 32)] .bool) fun _secb =>
  letV (.var (.succ (.succ .zero)) : Expr pqxdhOps [.bool, cpaStTy, .bool, .opt (B 32)] .bool) fun _b' =>
  letV (ahsfHybrid (.snd (.snd (.var (.succ (.succ .zero)) :
      Expr pqxdhOps [.bool, .bool, cpaStTy, .bool, .opt (B 32)] cpaStTy)))) fun _finalSt =>
  finalizeAuthFixedDsl S K

/-- Two-stage `ReductionDsl` program for `aeadCpaReductionAuthFixed` with list bound `K`. -/
def aeadCpaRedProg :
    TwoStageCostedReduction pqxdhOps pqPrimIface (authSpec S) (authCodec S)
      .unit .unit .bool cpaChOutTy (.opt (B 32)) .bool where
  σ          := cpaStTy
  π          := cpaPayloadTy
  init       := cpaInitC S K
  handlePre  := cpaPreC S K
  chDone     := cpaDefaultChC
  resume     := cpaResumeC
  handlePost := cpaPostC S K
  finish     := cpaFinishC S K

end Prog

end SignalPqxdh.Security.ReductionDsl.AuthAead
