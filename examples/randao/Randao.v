(* In this file we implement a RANDAO and prove it correct up to a
specification. In this version, uint256 is implemented as Z. 
However, uint32, 96, 16 is implemented as nat. 
*)

From Coq Require Import ZArith_base.
From Coq Require Import List. Import ListNotations.
From ConCert.Execution Require Import Blockchain.
From ConCert.Execution Require Import Containers.
From ConCert.Execution Require Import Monad.
From ConCert.Execution Require Import ResultMonad.
From ConCert.Execution Require Import Serializable.
From ConCert.Execution Require Import ContractCommon.
From ConCert.Utils Require Import RecordUpdate.

Section Randao.
  Context {BaseTypes : ChainBase}.

  Local Open Scope Z.
  Set Primitive Projections.

  Set Nonrecursive Elimination Schemes.

  Definition CampaignId := nat.

  Record Participant :=
    build_participant { 
      secret : Z;
      commitment : Z; 
      reward : Z;
      revealed : bool;
      rewarded : bool
    }. 

  Record Consumer :=
    build_consumer {
        consumer_addr : Address;          
        bountypot : Z
    }.   

  Record Campaign :=
    build_campaign {
    bnum : nat;
    deposit : nat;
    commitBalkline : nat;
    commitDeadline : nat;
    random : Z;
    settled : bool;
    bountypot_campaign : Z; 
    commitNum : nat;
    revealsNum : nat;
    consumers : FMap Address Consumer;
    participants : FMap Address Participant;
    commitments : FMap Z bool;
    }.

  Definition Setup := Z. 

  Definition Error : Type := nat.
  Definition default_error : Error := 1%nat.

  Inductive Msg :=
  | numCampaigns_msg : Msg
  | campaigns_msg : CampaignId -> Msg
  | founder_msg : Msg
  | getCommitment : CampaignId -> Msg
  | shaCommit : Z -> Msg
  | follow : CampaignId -> Msg
  | commit : CampaignId -> Z -> Msg
  | reveal : CampaignId -> Z -> Msg
  | getMyBounty : CampaignId -> Msg
  | getRandom : CampaignId -> Msg
  | newCampaign : nat -> nat -> nat -> nat -> Msg
  | refundBounty : CampaignId -> Msg.

  Record State :=
    build_state {
      numCampaigns : nat;
      campaigns : FMap CampaignId Campaign;
      founder : Address;
    }.

  (* begin hide *)
  MetaCoq Run (make_setters Participant).
  MetaCoq Run (make_setters Consumer).
  MetaCoq Run (make_setters Campaign).
  MetaCoq Run (make_setters State).
  (* end hide *)

  Section Serialization.

    Global Instance participant_serializable : Serializable Participant :=
      Derive Serializable Participant_rect <build_participant>.

    Global Instance consumer_serializable : Serializable Consumer :=
      Derive Serializable Consumer_rect <build_consumer>.
    
    Global Instance campaign_serializable : Serializable Campaign :=
      Derive Serializable Campaign_rect <build_campaign>.

    Global Instance msg_serializable : Serializable Msg :=
      Derive Serializable Msg_rect <numCampaigns_msg,
                                    campaigns_msg,
                                    founder_msg,
                                    getCommitment,
                                    shaCommit,
                                    follow,
                                    commit,
                                    reveal,
                                    getMyBounty,
                                    getRandom,
                                    newCampaign,
                                    refundBounty>.

    Global Instance state_serializable : Serializable State :=
      Derive Serializable State_rect <build_state>.

  End Serialization.

  Parameter hash_function : Z -> Z.
  Parameter null_address : Address.
  Axiom null_address_not_valid : forall ctx, address_eqb ctx.(ctx_from) null_address = false.
  (* Parameter zero_byte : Z.   *)

  Definition blankAddress (n : Address) : bool := negb (address_eqb n null_address).
  Definition moreThanZero (_deposit : nat) : bool := Z.of_nat _deposit <=? 0.
  Definition notBeBlank (_s : Z) : bool := (_s =? 0).
  Definition beBlank (_s : Z) : bool := negb (_s =? 0).
  Definition beFalse (_t : bool) : bool := _t.

  Definition timeLineCheck 
    (chain : Chain) (_bnum : nat) (_commitBalkline : nat) (_commitDeadline : nat) : bool := 
    (Z.of_nat chain.(chain_height) >=? Z.of_nat _bnum )
      || (Z.of_nat _commitBalkline <=? 0)
      || (Z.of_nat _commitDeadline <=? 0)
      || (Z.of_nat _commitDeadline >=? Z.of_nat _commitBalkline) 
      || (Z.of_nat chain.(chain_height) >=? Z.of_nat _bnum - Z.of_nat _commitBalkline).

  Definition newCampaign_body
    (chain : Chain) 
    (ctx : ContractCallContext)
    (state : State)
    (_bnum : nat) 
    (_deposit : nat)
    (_commitBalkline : nat) 
    (_commitDeadline : nat)
    : result (State * list ActionBody) Error :=
    do _ <- throwIf (timeLineCheck chain _bnum _commitBalkline _commitDeadline) default_error;
    do _ <- throwIf (moreThanZero _deposit) default_error;
    let _campaignID := Nat.add (FMap.size (state.(campaigns))) 1 in
    let consumer := {|
      consumer_addr := ctx.(ctx_from);
      bountypot := ctx.(ctx_amount);
    |} in
    let campaign := {|
      bnum := _bnum;
      deposit := _deposit;
      commitBalkline := _commitBalkline;
      commitDeadline := _commitDeadline;
      random := 0;
      settled := false;
      bountypot_campaign := ctx.(ctx_amount);
      commitNum := 0;
      revealsNum := 0;
      consumers := FMap.add ctx.(ctx_from) consumer FMap.empty;
      participants := FMap.empty;
      commitments := FMap.empty;
    |} in
    let result := _campaignID in
    Ok (state<|numCampaigns := S state.(numCampaigns)|> <|campaigns ::= FMap.add _campaignID campaign|>, []).

  Definition checkFollowPhase (chain : Chain) (_bnum : nat) (_commitDeadline : nat) : bool :=
    Z.of_nat (chain.(chain_height)) >? Z.of_nat _bnum - Z.of_nat _commitDeadline.

  Definition followCampaign
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    (c : Campaign)
    (consumer : Consumer)
    : result (State * list ActionBody) Error :=
    do _ <- throwIf (checkFollowPhase chain c.(bnum) c.(commitDeadline)) default_error;
    do _ <- throwIf (blankAddress consumer.(consumer_addr)) default_error;
    let c := c<|bountypot_campaign := c.(bountypot_campaign) + ctx.(ctx_amount)|> in (* += でやりたい *)
    let c := c<|consumers ::= FMap.add ctx.(ctx_from) {| consumer_addr := ctx.(ctx_from); bountypot := ctx.(ctx_amount); |}|> in
    let result := true in
    Ok (state<|campaigns ::= FMap.add _campaignID c|>, []).

  Definition follow_body
    (chain : Chain) 
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId) 
    : result (State * list ActionBody) Error :=
    do c <- result_of_option (FMap.find _campaignID state.(campaigns)) default_error;
    let (intermediate_state, consumer) := 
      match FMap.find ctx.(ctx_from) c.(consumers) with
      | Some consumer => (state, consumer)
      | None => 
        let c := c<|consumers ::= FMap.add ctx.(ctx_from) 
          {| consumer_addr := null_address; bountypot := 0; |} |> in
        (state<|campaigns ::= FMap.add _campaignID c|>, 
          {| consumer_addr := null_address; bountypot := 0; |}) 
      end in
    followCampaign chain ctx intermediate_state _campaignID c consumer.

  Definition checkDeposit (ctx : ContractCallContext) (_deposit : nat) : bool :=
    negb (ctx.(ctx_amount) =? Z.of_nat _deposit). 

  Definition checkCommitPhase 
    (chain : Chain) (_bnum : nat) (_commitBalkline : nat) (_commitDeadline : nat) : bool :=
    (Z.of_nat chain.(chain_height) <? Z.of_nat _bnum - Z.of_nat _commitBalkline )
      || (Z.of_nat chain.(chain_height) >? Z.of_nat _bnum - Z.of_nat _commitDeadline). 

  Definition commitmentCampaign 
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    (_hs : Z)
    (c : Campaign) : result (State * list ActionBody) Error :=
    do _ <- throwIf (checkDeposit ctx c.(deposit)) default_error;
    do _ <- throwIf (checkCommitPhase chain c.(bnum) c.(commitBalkline) c.(commitDeadline)) default_error;  
    let (intermediate_state1, participant) := match FMap.find ctx.(ctx_from) c.(participants) with
      | Some participant => (state, participant)
      | None => 
        let c := c<| participants ::= FMap.add ctx.(ctx_from) {| secret := 0; commitment := 0; reward := 0; revealed := false; rewarded := false |} |> in
        (state<|campaigns ::= FMap.add _campaignID c|>, {| secret := 0; commitment := 0; reward := 0; revealed := false; rewarded := false |})
      end in
    do _ <- throwIf (beBlank participant.(commitment)) default_error;
    let (intermediate_state2, commitmentb) := match FMap.find _hs c.(commitments) with
      | Some b => (intermediate_state1, b) 
      | None => 
        let c := c<| commitments ::= FMap.add _hs false |> in
        (intermediate_state1<|campaigns ::= FMap.add _campaignID c|>, false)
      end in
    do _ <- throwIf commitmentb default_error; 
    let participant := {|
      secret := 0;
      commitment := _hs;
      reward := 0;
      revealed := false;
      rewarded := false;
    |} in
    let c := c <|participants ::= FMap.add ctx.(ctx_from) participant|> in
    let c := c <|commitNum := Nat.add c.(commitNum) 1 |> in
    let c := c <|commitments ::= FMap.add _hs true |> in 
    Ok (intermediate_state2<|campaigns ::= FMap.add _campaignID c|>, []).

  Definition commit_body
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    (_hs : Z) : result (State * list ActionBody) Error :=
    do _ <- throwIf (notBeBlank _hs) default_error;
    do c <- result_of_option (FMap.find _campaignID state.(campaigns)) default_error;
    commitmentCampaign chain ctx state _campaignID _hs c.

  Definition getCommitment_body
    (chain : Chain) 
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId) : result (State * list ActionBody) Error :=
    do c <- result_of_option (FMap.find _campaignID state.(campaigns)) default_error;
    do participant <- result_of_option (FMap.find ctx.(ctx_from) c.(participants)) default_error;
    let result := participant.(commitment) in
    Ok (state, []). 

  Definition shaCommit_body (state : State) (_s : Z) : result (State * list ActionBody) Error :=
    let result := hash_function _s in
    Ok (state, []).

  Definition checkRevealPhase 
    (chain : Chain) (_bnum : nat) (_commitDeadline : nat) : bool :=
  (Z.of_nat chain.(chain_height) <=? Z.of_nat _bnum - Z.of_nat _commitDeadline )
    || (Z.of_nat chain.(chain_height) >=? Z.of_nat _bnum).

  Definition checkSercret
    (_s : Z) (commitment : Z) : bool :=
    negb (commitment =? hash_function _s).

  Definition revealCampaign 
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    (_s : Z)
    (c : Campaign)
    (p : Participant)
    : result (State * list ActionBody) Error :=
    do _ <- throwIf (checkRevealPhase chain c.(bnum) c.(commitDeadline)) default_error;
    do _ <- throwIf (checkSercret _s p.(commitment)) default_error; 
    do _ <- throwIf (beFalse p.(revealed)) default_error;
    let p := p <| secret := _s |> in
    let p := p <| revealed := true |> in
    let c := c <| revealsNum := Nat.add c.(revealsNum) 1 |> in
    let c := c <| random := c.(random) + p.(secret) |> in 
    let c := c <|participants ::= FMap.add ctx.(ctx_from) p|> in
    Ok (state<|campaigns ::= FMap.add _campaignID c|>, []).

  Definition reveal_body
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    (_s : Z)
    : result (State * list ActionBody) Error :=
    do c <- result_of_option (FMap.find _campaignID state.(campaigns)) default_error;
    do p <- result_of_option (FMap.find ctx.(ctx_from) c.(participants)) default_error;
    revealCampaign chain ctx state _campaignID _s c p.

  Definition bountyPhase (chain : Chain) (_bnum : nat) : bool :=
    Z.of_nat chain.(chain_height) <? Z.of_nat _bnum.

  Definition returnRandom (chain : Chain) (c : Campaign) : result Z Error :=
    do _ <- throwIf (bountyPhase chain c.(bnum)) default_error;
    if Nat.eqb c.(revealsNum) c.(commitNum) then 
      let c := c<|settled := true|> in
      Ok c.(random)
    else Err default_error.

  Definition getRandom_body (chain : Chain) (state : State) (_campaignID : CampaignId) 
    : result (State * list ActionBody) Error :=
    do c <- result_of_option (FMap.find _campaignID state.(campaigns)) default_error;
    let result := returnRandom chain c in
    Ok (state, []).

  Definition fines (c : Campaign) : Z :=
    (Z.of_nat c.(commitNum) - Z.of_nat c.(revealsNum)) * (Z.of_nat c.(deposit)).

  Definition calculateShare (c : Campaign) : Z :=
    if (Z.of_nat c.(commitNum) >? Z.of_nat c.(revealsNum)) then 
      fines c / Z.of_nat c.(revealsNum)
    else 
      c.(bountypot_campaign) / Z.of_nat c.(revealsNum).

   Definition returnReward 
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    (_share : Z)
    (c : Campaign)
    (p : Participant)
    : result (State * list ActionBody) Error :=
    let p := p <| reward := _share |> in 
    let p := p <| rewarded := true |> in 
    let c := c <|participants ::= FMap.add ctx.(ctx_from) p|> in
    Ok (state<|campaigns ::= FMap.add _campaignID c|>, 
        [act_transfer ctx.(ctx_from) (_share + Z.of_nat c.(deposit))]).

  Definition transferBounty 
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    (c : Campaign)
    (p : Participant)
    : result (State * list ActionBody) Error :=
    do _ <- throwIf (bountyPhase chain c.(bnum)) default_error;
    do _ <- throwIf (beFalse p.(rewarded)) default_error;
    if Z.of_nat c.(revealsNum) >? 0 then
      (
        if p.(revealed) then  
          let share := calculateShare c in
          returnReward ctx state _campaignID share c p
        else 
          Err default_error (* coq は else 無しはダメ *)
      )
    else 
      returnReward ctx state _campaignID 0 c p.

  Definition getMyBounty_body 
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId)
    : result (State * list ActionBody) Error :=
    do c <- result_of_option (FMap.find _campaignID state.(campaigns)) default_error;
    do p <- result_of_option (FMap.find ctx.(ctx_from) c.(participants)) default_error;
    transferBounty chain ctx state _campaignID c p.

  Definition campaignFailed (_commitNum : nat) (_revealsNum : nat) : bool :=
    (Nat.eqb _commitNum _revealsNum) && (negb (Nat.eqb _commitNum 0)).

  Definition beConsumer (ctx : ContractCallContext) (_caddr : Address) : bool :=
    negb (address_eqb _caddr ctx.(ctx_from)).

  Definition returnBounty
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)
    (_campaignID : CampaignId) 
    (c : Campaign)
    : result (State * list ActionBody) Error :=
    do _ <- throwIf (bountyPhase chain c.(bnum)) default_error;
    do _ <- throwIf (campaignFailed c.(commitNum) c.(revealsNum)) default_error;
    do consumer <- result_of_option (FMap.find ctx.(ctx_from) c.(consumers)) default_error;
    do _ <- throwIf (beConsumer ctx consumer.(consumer_addr) ) default_error;
    
    let _bountypot := consumer.(bountypot) in 
    let consumer := consumer<| bountypot := 0 |> in
    let c := c <| consumers ::= FMap.add ctx.(ctx_from) consumer |> in
    Ok (state <|campaigns ::= FMap.add _campaignID c|>, 
        [act_transfer ctx.(ctx_from) _bountypot]).

  (* Campaign 失敗時, Consumerに報奨金を返金. Consumer が呼び出す *)
  Definition refundBounty_body 
    (chain : Chain)
    (ctx : ContractCallContext)
    (state : State)

    (_campaignID : CampaignId)
    : result (State * list ActionBody) Error :=
    do c <- result_of_option (FMap.find _campaignID state.(campaigns)) default_error;
    returnBounty chain ctx state _campaignID c.
  
  Definition init    
      (chain : Chain) 
      (ctx : ContractCallContext) 
      (setup : Setup)      
      : result State Error :=
      Ok {|
        numCampaigns := 0;
        campaigns := FMap.empty;
        founder := ctx.(ctx_from);
      |}.

  Definition receive
            (chain : Chain)
            (ctx : ContractCallContext)
            (state : State)
            (maybe_msg : option Msg)
            : result (State * list ActionBody) Error :=
    let sender := ctx.(ctx_from) in
    match maybe_msg with
    | Some (newCampaign _bnum _deposit _commitBalkline _commitDeadline) =>
      newCampaign_body chain ctx state  _bnum _deposit _commitBalkline _commitDeadline
    | Some (follow _campaignID) =>
      follow_body chain ctx state _campaignID
    | Some (commit _campaignID _hs) =>
      commit_body chain ctx state _campaignID _hs
    | Some (getCommitment _campaignID) =>
      getCommitment_body chain ctx state _campaignID
    | Some (shaCommit _s) =>
      shaCommit_body state _s  
    | Some (reveal _campaignID _s) =>
      reveal_body chain ctx state _campaignID _s
    | Some (getRandom _campaignID) =>
      getRandom_body chain state _campaignID
    | Some (getMyBounty _campaignID) =>
      getMyBounty_body chain ctx state _campaignID
    | Some (refundBounty _campaignID) =>
      refundBounty_body chain ctx state _campaignID
    | Some (numCampaigns_msg) =>
      let result := state.(numCampaigns) in
      Ok (state, [])
    | Some (campaigns_msg n) =>
      do result <- result_of_option (FMap.find n state.(campaigns)) default_error : result Campaign Error; 
      Ok (state, [])
    | Some (founder_msg) =>
      let result := state.(founder) in 
      Ok (state, [])
    | _ =>
          Err default_error
    end.

  Definition contract : Contract Setup Msg State Error :=
    build_contract init receive.
End Randao.

From Coq Require Import Psatz.
From ConCert.Utils Require Import Automation.
From ConCert.Utils Require Import Extras.
From Coq Require Import Permutation.

Section Theories.
  Context {BaseTypes : ChainBase}.

  Local Open Scope Z.

  (* debug  *)
  Set Ltac Backtrace.

  Definition afterFirstPhase (chain : Chain) (campaign : Campaign) : Prop :=
    Z.of_nat chain.(chain_height) >? Z.of_nat campaign.(bnum) - Z.of_nat campaign.(commitDeadline) = true.

  Definition ThirdPhase (chain : Chain) (campaign : Campaign) : Prop :=
    bountyPhase chain campaign.(bnum) = false.

  Definition RNG_fail (chain : Chain) (campaign : Campaign) : Prop :=
    bountyPhase chain campaign.(bnum) = false /\ 
    (Nat.eqb campaign.(commitNum) campaign.(revealsNum) = false \/
     negb (Nat.eqb campaign.(commitNum) 0) = false).

  Lemma ThirdPhase_is_bountyphase (chain : Chain) (campaign : Campaign) : 
    ThirdPhase chain campaign -> bountyPhase chain campaign.(bnum) = false.
  Proof.
    unfold ThirdPhase. auto.
  Qed.

  Lemma contraPhase_commit_reveal (chain : Chain) (campaign : Campaign) :
    ~ (
      checkCommitPhase chain campaign.(bnum) campaign.(commitBalkline) campaign.(commitDeadline) = false /\
      checkRevealPhase chain campaign.(bnum) campaign.(commitDeadline)  = false
    ).
  Proof. 
    unfold checkCommitPhase, checkRevealPhase. intros [H1 H2]. apply Bool.orb_false_elim in H1 as [_ H1]. apply Bool.orb_false_elim in H2 as [H2 _].
    unfold Z.gtb, Z.leb in *. 
    destruct (Z.of_nat (chain_height chain) ?= Z.of_nat (bnum campaign) - Z.of_nat (commitDeadline campaign)); auto. 
  Qed.

  Lemma contraPhase_reveal_bounty (chain : Chain) (campaign : Campaign) :
    ~ (
      checkRevealPhase chain campaign.(bnum) campaign.(commitDeadline) = false /\
      bountyPhase chain campaign.(bnum) = false
    ).
  Proof.
    unfold checkRevealPhase, bountyPhase. intros [H1 H2]. apply Bool.orb_false_elim in H1 as [_ H1].
    unfold Z.geb, Z.ltb in *.
    destruct (Z.of_nat (chain_height chain) ?= Z.of_nat (bnum campaign)); auto.
  Qed. 

  Lemma contraPhase_commit_bounty (chain : Chain) (campaign : Campaign) :
  (Z.of_nat campaign.(commitDeadline) <=? 0) = false ->
    ~ (
      checkCommitPhase chain campaign.(bnum) campaign.(commitBalkline) campaign.(commitDeadline) = false /\
      bountyPhase chain campaign.(bnum) = false
    ).
  Proof.
    unfold checkCommitPhase, bountyPhase. lia. Qed.

  Lemma contraPhase_follow_bounty (chain : Chain) (campaign : Campaign) :
  (Z.of_nat campaign.(commitDeadline) <=? 0) = false ->
    ~ (
      checkFollowPhase chain campaign.(bnum) campaign.(commitDeadline) = false /\
      bountyPhase chain campaign.(bnum) = false
    ).
  Proof.
    unfold checkFollowPhase, bountyPhase. lia. Qed.

  (*
    1
    The first phase, if two or more of the same sha3(s) are submitted in sequence, 
    only the first one is accepted.
  *)

  Theorem hash_is_dictinct (chain : Chain) (ctx : ContractCallContext) (state : State) (campaignID : CampaignId) (hs : Z) :
    forall (campaign : Campaign), 
      FMap.find campaignID state.(campaigns) = Some campaign ->
      FMap.find hs campaign.(commitments) = Some true ->
      commit_body chain ctx state campaignID hs = Err default_error.
  Proof.
    intros. unfold commit_body. rewrite H. cbn.
    destruct (notBeBlank hs) eqn:Hr1; cbn; auto.
    destruct (checkDeposit ctx campaign.(deposit)) eqn:Hr2; cbn; auto.
    destruct (checkCommitPhase chain campaign.(bnum) campaign.(commitBalkline) campaign.(commitDeadline)) eqn:Hr3; cbn; auto.
    destruct (FMap.find (ctx_from ctx) campaign.(participants)) eqn:Hr4.
    + destruct (beBlank p.(commitment)) eqn:Hr5; cbn; auto.
      rewrite H0. auto.
    + cbn. rewrite H0. auto. 
  Qed.

  (*
    2
    The first phase, there is a requirement for minimum number of participants, 
    if it fails to collect enough sha3(s) within the time period, 
    then RNG at this block height will fail.
  *)

  Lemma not_enough_commit block_state randao_addr (trace : ChainTrace empty_state block_state) :
    env_contracts block_state randao_addr = Some (contract : WeakContract) ->
    exists (cstate : State) (call_info : list (ContractCallInfo Msg)) (deploy_info : DeploymentInfo Setup),
      contract_state block_state randao_addr = Some cstate /\
      incoming_calls Msg trace randao_addr = Some call_info /\
      deployment_info _ trace randao_addr = Some deploy_info /\
      (
        fun   (chain_height : nat)
              (current_slot : nat)
              (finalized_height : nat)
              (caddr : Address)
              (deployment_info : DeploymentInfo Setup)
              (contract_state : State)
              (balance : Amount)
              (outgoing_actions_queued : list ActionBody)
              (incoming_calls_seen : list (ContractCallInfo Msg))
              (outgoing_txs_seen : list Tx) =>
        forall (campaignID : CampaignId) (campaign : Campaign),
          FMap.find campaignID cstate.(campaigns) = Some campaign ->
          (* Add Block の場合が突破できないため, 保留 *)
          (* afterFirstPhase chain_height campaign -> *)
          (
            (* 補題 *)
            (
              (* 補題1 *)
             forall (hs : Z) (b : bool), 
               FMap.find hs campaign.(commitments) = Some b ->
               b = true
            ) /\
            (
             (* 補題2, 3 *)
              forall (call_origin : Address) (call_from : Address) (call_amount : Amount),
                let ctx := {| ctx_origin := call_origin;
                              ctx_from := call_from;
                              ctx_contract_address := caddr;
                              ctx_contract_balance := balance;
                              ctx_amount := call_amount |} in
                (
                  forall (consumer : Consumer),
                    FMap.find ctx.(ctx_from) campaign.(consumers) = Some consumer ->
                    consumer.(consumer_addr) = ctx.(ctx_from)
                ) /\
                (
                  forall (participant : Participant),
                    FMap.find ctx.(ctx_from) campaign.(participants) = Some participant ->
                    participant.(commitment) =? 0 = false                  
                )
            )
          ) /\
          (
            Nat.eqb campaign.(commitNum) 0 = true ->
            campaign.(participants) = FMap.empty /\ (* 補題4 *)
            campaign.(random) = 0 (* 本命 *)
          )
      )
        (chain_height block_state)
        (current_slot block_state)
        (finalized_height block_state)
        randao_addr
        deploy_info
        cstate
        (env_account_balances block_state randao_addr)
        (outgoing_acts block_state randao_addr)
        call_info
        (outgoing_txs trace randao_addr).
  Proof.
    contract_induction; intros. 
    - (* AddBlock *)
      apply (IH campaignID campaign H).
    - (* Deploy *)
      inversion init_some. rewrite <- H1 in H. discriminate H. 
    - (* outgoing call *)
      apply (IH campaignID campaign H).
    - (* non recursive incoming call *) 
      destruct msg as [msg|]; simpl in receive_some; try discriminate receive_some.
      destruct msg eqn:MSG; cbn in receive_some. 
      + (* numCampaigns *)
        inversion receive_some. rewrite H1 in *. apply (IH campaignID campaign H).
      + (* campaigns *)
        destruct (result_of_option (FMap.find c (campaigns prev_state)) default_error); inversion receive_some.
        rewrite H1 in *. apply (IH campaignID campaign H).
      + (* founder *)
        inversion receive_some. rewrite H1 in *. apply (IH campaignID campaign H).
      + (* msg = getCommitment *)
        destruct (FMap.find c (campaigns prev_state)) eqn:H2; cbn in receive_some; try discriminate receive_some. (* c に型注釈をすると修正前でも行ける *)
        destruct (result_of_option (FMap.find (ctx_from ctx) (participants c0)) default_error) eqn:H3; cbn in receive_some; try discriminate receive_some.
        inversion receive_some. rewrite H1 in *.
        apply (IH campaignID campaign H).
      + (* shaCommit *)
        unfold shaCommit_body in receive_some. inversion receive_some.
        rewrite H1 in *. apply (IH campaignID campaign H).
      + (* follow *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr2; cbn in receive_some.
        {
          (* 二重 follow はできない *)
          destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
          destruct (blankAddress (consumer_addr c1)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
          unfold blankAddress in Hr4.
          specialize (IH c c0 Hr1) as [[_ IH] _]. 
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [IH _]. 
          specialize (IH c1 Hr2). cbn in IH.
          rewrite IH in Hr4. rewrite null_address_not_valid in Hr4. discriminate Hr4.
        }
        destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        unfold blankAddress in receive_some. rewrite address_eq_refl in receive_some. cbn in receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers in receive_some; cbn in receive_some.
        rewrite FMap.add_add in receive_some. inversion receive_some.        
        rewrite <- H1 in H. cbn in H.

        split. (* 補題1の証明 *)
        {
          destruct (Nat.eqb c campaignID) eqn:B; intros; cbn in *.
          - apply Nat.eqb_eq in B. rewrite B in *.
            rewrite FMap.find_add in H. inversion H. rewrite <- H3 in *. cbn in *.
            specialize (IH campaignID c0 Hr1) as [IH _].
            repeat split; try (apply IH; auto). intros.
            specialize IH as [_ IH].
            specialize (IH call_origin call_from call_amount) as [IH _]. 
            destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
              rewrite B' in *. rewrite FMap.find_add in H0. inversion H0. auto.  
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
              rewrite FMap.find_add_ne in H0; auto.
          - apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H; auto.
            apply (IH campaignID campaign H); auto.
        }
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. inversion H. cbn.
          apply (IH campaignID c0 Hr1).
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H; auto. 
          apply (IH campaignID campaign H).
      + (* commit *)
        destruct (notBeBlank z) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkDeposit ctx (deposit c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkCommitPhase chain (bnum c0) (commitBalkline c0) (commitDeadline c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        { 
          (* 二重 commit *)
          destruct (beBlank (commitment p)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          specialize (IH c c0 Hr2) as [[_ IH] _]. 
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [_ IH].
          unfold beBlank in Hr6. rewrite IH in Hr6; auto. discriminate Hr6.
        }
        destruct (FMap.find z (commitments c0)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
        {
          (* commitments が存在 *)
          specialize (IH c c0 Hr2) as [[IH _] _].
          specialize (IH z b). rewrite IH in receive_some; auto. cbn in receive_some; discriminate receive_some.
        }
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_commitments, set_Campaign_commitments,
          setter_from_getter_Campaign_commitNum, set_Campaign_commitNum, setter_from_getter_Campaign_participants, set_Campaign_participants in receive_some; cbn in receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in H.
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. inversion H. cbn in *.
          specialize (IH campaignID c0 Hr2).
          split.
          {
            split. 
            - (* commmitmentb が true *)
              intros. destruct (Z.eqb hs z) eqn:B1.
              + apply Z.eqb_eq in B1. rewrite B1 in *. rewrite FMap.find_add in H0. inversion H0. auto.
              + apply Z.eqb_neq in B1. rewrite FMap.find_add_ne in H0; auto. 
                specialize IH as [[IH _] _]. apply (IH hs); auto.
            - specialize IH as [[_ IH] _]. split. apply IH; auto. intros.
            destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
              rewrite B' in *. rewrite FMap.find_add in H0. inversion H0. auto.  
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
              rewrite FMap.find_add_ne in H0; auto. 
              apply (IH call_origin call_from call_amount); auto.
          } 
          rewrite Nat.add_comm. discriminate.  
        * apply Nat.eqb_neq in B. 
          repeat (rewrite FMap.find_add_ne in H; auto).
          apply (IH campaignID campaign H).
      + (* reveal *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkRevealPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkSercret z (commitment p)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (beFalse (revealed p)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants,
          set_Campaign_participants, setter_from_getter_Participant_revealed, set_Participant_revealed, setter_from_getter_Participant_secret, set_Participant_secret in receive_some; cbn in receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in *. 
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *. 
          rewrite FMap.find_add in H. inversion H. cbn. 
          split.
          {
            repeat split; try apply (IH campaignID c0 Hr1); auto.
            specialize (IH campaignID c0 Hr1) as [[_ IH] _]. 
            intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
              rewrite <- B' in *. rewrite FMap.find_add in H0. inversion H0. cbn. 
              apply (IH call_origin call_from call_amount); auto.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
              rewrite FMap.find_add_ne in H0; auto. apply (IH call_origin call_from call_amount); auto.
          }
          (* 矛盾を導く *)
          intros. specialize (IH campaignID c0 Hr1) as [_ [contra _]]; auto. 
          rewrite contra in Hr2. rewrite FMap.find_empty in Hr2. discriminate Hr2.
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H by apply B. 
          apply (IH campaignID campaign H).
      + (* getMyBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (beFalse (rewarded p)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (Z.of_nat (revealsNum c0) >? 0) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        * destruct (revealed p) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          unfold returnReward in receive_some. cbn in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, 
            set_Campaign_participants, setter_from_getter_Participant_rewarded, set_Participant_rewarded, setter_from_getter_Participant_reward, set_Participant_reward in receive_some; cbn in receive_some.
          inversion receive_some. rewrite <- H1 in H. cbn in H. 
          destruct (Nat.eqb c campaignID) eqn:B.
          -- apply Nat.eqb_eq in B. rewrite B in *.
            rewrite FMap.find_add in H. inversion H. cbn in *. split; intros.
            {
              (* Lemma *)
              repeat split; try apply (IH campaignID c0 Hr1); auto.
              specialize (IH campaignID c0 Hr1) as [[_ IH] _]. 
              intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                rewrite <- B' in *. rewrite FMap.find_add in H0. inversion H0. cbn. 
                apply (IH call_origin call_from call_amount); auto.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                rewrite FMap.find_add_ne in H0; auto. apply (IH call_origin call_from call_amount); auto.
            }
            destruct (IH campaignID c0 Hr1) as [_ [contra _]]; auto. 
            rewrite contra in Hr2. rewrite FMap.find_empty in Hr2. discriminate Hr2.
          -- apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
        * unfold returnReward in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, 
            set_Campaign_participants, setter_from_getter_Participant_rewarded, set_Participant_rewarded, setter_from_getter_Participant_reward, set_Participant_reward in receive_some; cbn in receive_some.
          inversion receive_some. rewrite <- H1 in H. cbn in H.
          destruct (Nat.eqb c campaignID) eqn:B.
          -- apply Nat.eqb_eq in B. rewrite B in *.
            rewrite FMap.find_add in H. inversion H. cbn in *. split; intros.
            {
              (* Lemma *)
              repeat split; try apply (IH campaignID c0 Hr1); auto.
              specialize (IH campaignID c0 Hr1) as [[_ IH] _]. 
              intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                rewrite <- B' in *. rewrite FMap.find_add in H0. inversion H0. cbn. 
                apply (IH call_origin call_from call_amount); auto.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                rewrite FMap.find_add_ne in H0; auto. apply (IH call_origin call_from call_amount); auto.
            }
            destruct (IH campaignID c0) as [_ [contra _]]; auto. 
            rewrite contra, FMap.find_empty in Hr2. discriminate Hr2.
          -- apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
      + (* getRandom *)
        destruct (FMap.find c (campaigns prev_state)) eqn:H1; cbn in receive_some; try discriminate receive_some.
        inversion receive_some; rewrite H2 in *; apply (IH campaignID campaign H).
      + (* newCampaign *)
        destruct (timeLineCheck chain n n1 n2) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (moreThanZero n0) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in *.
        destruct (Nat.eqb ((FMap.size (campaigns prev_state) + 1)%nat) campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. cbn in H. inversion H. cbn.
          repeat split; try rewrite FMap.find_empty; try discriminate; auto.
          intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. rewrite B' in *.
            rewrite FMap.find_add in H0. inversion H0; auto.
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
            rewrite FMap.find_add_ne in H0; auto. rewrite FMap.find_empty in H0. discriminate H0.
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
      + (* returnBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (campaignFailed (commitNum c0) (revealsNum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (throwIf (beConsumer ctx (consumer_addr c1)) default_error) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers, 
          setter_from_getter_Consumer_bountypot, set_Consumer_bountypot in receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in *. 
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. inversion H. cbn.
          specialize (IH campaignID c0 Hr1) as IH. 
          repeat split; try apply IH; auto.
          intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. rewrite B' in *.
            rewrite FMap.find_add in H0. inversion H0. cbn. apply IH; auto. 
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
            rewrite FMap.find_add_ne in H0; auto. apply IH; auto.
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
    - (* recursive *)
      destruct msg as [msg|]; simpl in receive_some; try discriminate receive_some.
      destruct msg eqn:MSG; cbn in receive_some. 
      + (* numCampaigns *)
        inversion receive_some. rewrite H1 in *. apply (IH campaignID campaign H).
      + (* campaigns *)
        destruct (result_of_option (FMap.find c (campaigns prev_state)) default_error); inversion receive_some.
        rewrite H1 in *. apply (IH campaignID campaign H).
      + (* founder *)
        inversion receive_some. rewrite H1 in *. apply (IH campaignID campaign H).
      + (* msg = getCommitment *)
        destruct (FMap.find c (campaigns prev_state)) eqn:H2; cbn in receive_some; try discriminate receive_some. (* c に型注釈をすると修正前でも行ける *)
        destruct (result_of_option (FMap.find (ctx_from ctx) (participants c0)) default_error) eqn:H3; cbn in receive_some; try discriminate receive_some.
        inversion receive_some. rewrite H1 in *.
        apply (IH campaignID campaign H).
      + (* shaCommit *)
        unfold shaCommit_body in receive_some. inversion receive_some.
        rewrite H1 in *. apply (IH campaignID campaign H).
      + (* follow *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr2; cbn in receive_some.
        {
          (* 二重 follow はできない *)
          destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
          destruct (blankAddress (consumer_addr c1)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
          unfold blankAddress in Hr4.
          specialize (IH c c0 Hr1) as [[_ IH] _]. 
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [IH _]. 
          specialize (IH c1 Hr2). cbn in IH.
          rewrite IH in Hr4. rewrite null_address_not_valid in Hr4. discriminate Hr4.
        }
        destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        unfold blankAddress in receive_some. rewrite address_eq_refl in receive_some. cbn in receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers in receive_some; cbn in receive_some.
        rewrite FMap.add_add in receive_some. inversion receive_some.        
        rewrite <- H1 in H. cbn in H.

        split. (* 補題1の証明 *)
        {
          destruct (Nat.eqb c campaignID) eqn:B; intros; cbn in *.
          - apply Nat.eqb_eq in B. rewrite B in *.
            rewrite FMap.find_add in H. inversion H. rewrite <- H3 in *. cbn in *.
            specialize (IH campaignID c0 Hr1) as [IH _].
            repeat split; try (apply IH; auto). intros.
            specialize IH as [_ IH].
            specialize (IH call_origin call_from call_amount) as [IH _]. 
            destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
              rewrite B' in *. rewrite FMap.find_add in H0. inversion H0. auto.  
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
              rewrite FMap.find_add_ne in H0; auto.
          - apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H; auto.
            apply (IH campaignID campaign H); auto.
        }
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. inversion H. cbn.
          apply (IH campaignID c0 Hr1).
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H; auto. 
          apply (IH campaignID campaign H).
      + (* commit *)
        destruct (notBeBlank z) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkDeposit ctx (deposit c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkCommitPhase chain (bnum c0) (commitBalkline c0) (commitDeadline c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        { 
          (* 二重 commit *)
          destruct (beBlank (commitment p)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          specialize (IH c c0 Hr2) as [[_ IH] _]. 
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [_ IH].
          unfold beBlank in Hr6. rewrite IH in Hr6; auto. discriminate Hr6.
        }
        destruct (FMap.find z (commitments c0)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
        {
          (* commitments が存在 *)
          specialize (IH c c0 Hr2) as [[IH _] _].
          specialize (IH z b). rewrite IH in receive_some; auto. cbn in receive_some; discriminate receive_some.
        }
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_commitments, set_Campaign_commitments,
          setter_from_getter_Campaign_commitNum, set_Campaign_commitNum, setter_from_getter_Campaign_participants, set_Campaign_participants in receive_some; cbn in receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in H.
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. inversion H. cbn in *.
          specialize (IH campaignID c0 Hr2).
          split.
          {
            split. 
            - (* commmitmentb が true *)
              intros. destruct (Z.eqb hs z) eqn:B1.
              + apply Z.eqb_eq in B1. rewrite B1 in *. rewrite FMap.find_add in H0. inversion H0. auto.
              + apply Z.eqb_neq in B1. rewrite FMap.find_add_ne in H0; auto. 
                specialize IH as [[IH _] _]. apply (IH hs); auto.
            - specialize IH as [[_ IH] _]. split. apply IH; auto. intros.
            destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
              rewrite B' in *. rewrite FMap.find_add in H0. inversion H0. auto.  
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
              rewrite FMap.find_add_ne in H0; auto. 
              apply (IH call_origin call_from call_amount); auto.
          } 
          rewrite Nat.add_comm. discriminate.  
        * apply Nat.eqb_neq in B. 
          repeat (rewrite FMap.find_add_ne in H; auto).
          apply (IH campaignID campaign H).
      + (* reveal *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkRevealPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkSercret z (commitment p)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (beFalse (revealed p)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants,
          set_Campaign_participants, setter_from_getter_Participant_revealed, set_Participant_revealed, setter_from_getter_Participant_secret, set_Participant_secret in receive_some; cbn in receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in *. 
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *. 
          rewrite FMap.find_add in H. inversion H. cbn. 
          split.
          {
            repeat split; try apply (IH campaignID c0 Hr1); auto.
            specialize (IH campaignID c0 Hr1) as [[_ IH] _]. 
            intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
              rewrite <- B' in *. rewrite FMap.find_add in H0. inversion H0. cbn. 
              apply (IH call_origin call_from call_amount); auto.
            + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
              rewrite FMap.find_add_ne in H0; auto. apply (IH call_origin call_from call_amount); auto.
          }
          (* 矛盾を導く *)
          intros. specialize (IH campaignID c0 Hr1) as [_ [contra _]]; auto. 
          rewrite contra in Hr2. rewrite FMap.find_empty in Hr2. discriminate Hr2.
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H by apply B. 
          apply (IH campaignID campaign H).
      + (* getMyBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (beFalse (rewarded p)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (Z.of_nat (revealsNum c0) >? 0) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        * destruct (revealed p) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          unfold returnReward in receive_some. cbn in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, 
            set_Campaign_participants, setter_from_getter_Participant_rewarded, set_Participant_rewarded, setter_from_getter_Participant_reward, set_Participant_reward in receive_some; cbn in receive_some.
          inversion receive_some. rewrite <- H1 in H. cbn in H. 
          destruct (Nat.eqb c campaignID) eqn:B.
          -- apply Nat.eqb_eq in B. rewrite B in *.
            rewrite FMap.find_add in H. inversion H. cbn in *. split; intros.
            {
              (* Lemma *)
              repeat split; try apply (IH campaignID c0 Hr1); auto.
              specialize (IH campaignID c0 Hr1) as [[_ IH] _]. 
              intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                rewrite <- B' in *. rewrite FMap.find_add in H0. inversion H0. cbn. 
                apply (IH call_origin call_from call_amount); auto.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                rewrite FMap.find_add_ne in H0; auto. apply (IH call_origin call_from call_amount); auto.
            }
            destruct (IH campaignID c0 Hr1) as [_ [contra _]]; auto. 
            rewrite contra in Hr2. rewrite FMap.find_empty in Hr2. discriminate Hr2.
          -- apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
        * unfold returnReward in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, 
            set_Campaign_participants, setter_from_getter_Participant_rewarded, set_Participant_rewarded, setter_from_getter_Participant_reward, set_Participant_reward in receive_some; cbn in receive_some.
          inversion receive_some. rewrite <- H1 in H. cbn in H.
          destruct (Nat.eqb c campaignID) eqn:B.
          -- apply Nat.eqb_eq in B. rewrite B in *.
            rewrite FMap.find_add in H. inversion H. cbn in *. split; intros.
            {
              (* Lemma *)
              repeat split; try apply (IH campaignID c0 Hr1); auto.
              specialize (IH campaignID c0 Hr1) as [[_ IH] _]. 
              intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                rewrite <- B' in *. rewrite FMap.find_add in H0. inversion H0. cbn. 
                apply (IH call_origin call_from call_amount); auto.
              + destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                rewrite FMap.find_add_ne in H0; auto. apply (IH call_origin call_from call_amount); auto.
            }
            destruct (IH campaignID c0) as [_ [contra _]]; auto. 
            rewrite contra, FMap.find_empty in Hr2. discriminate Hr2.
          -- apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
      + (* getRandom *)
        destruct (FMap.find c (campaigns prev_state)) eqn:H1; cbn in receive_some; try discriminate receive_some.
        inversion receive_some; rewrite H2 in *; apply (IH campaignID campaign H).
      + (* newCampaign *)
        destruct (timeLineCheck chain n n1 n2) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (moreThanZero n0) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in *.
        destruct (Nat.eqb ((FMap.size (campaigns prev_state) + 1)%nat) campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. cbn in H. inversion H. cbn.
          repeat split; try rewrite FMap.find_empty; try discriminate; auto.
          intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. rewrite B' in *.
            rewrite FMap.find_add in H0. inversion H0; auto.
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
            rewrite FMap.find_add_ne in H0; auto. rewrite FMap.find_empty in H0. discriminate H0.
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
      + (* returnBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (campaignFailed (commitNum c0) (revealsNum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (throwIf (beConsumer ctx (consumer_addr c1)) default_error) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers, 
          setter_from_getter_Consumer_bountypot, set_Consumer_bountypot in receive_some.
        inversion receive_some. rewrite <- H1 in *. cbn in *. 
        destruct (Nat.eqb c campaignID) eqn:B.
        * apply Nat.eqb_eq in B. rewrite B in *.
          rewrite FMap.find_add in H. inversion H. cbn.
          specialize (IH campaignID c0 Hr1) as IH. 
          repeat split; try apply IH; auto.
          intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. rewrite B' in *.
            rewrite FMap.find_add in H0. inversion H0. cbn. apply IH; auto. 
          -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
            rewrite FMap.find_add_ne in H0; auto. apply IH; auto.
        * apply Nat.eqb_neq in B. 
          rewrite FMap.find_add_ne in H by apply B. apply (IH campaignID campaign H).
    - (* Permutation *)
      apply (IH campaignID campaign H).
    - (* Facts *)
      instantiate (CallFacts := fun _ _ _ _ _ => True).
      instantiate (AddBlockFacts := fun _ _ _ _ _ _ => True).
      instantiate (DeployFacts := fun _ _ => True).
      unset_all. subst. 
      destruct_chain_step; auto.
      destruct_action_eval; auto.
  Qed.

  Theorem not_enough_commit_simpl block_state randao_addr (trace : ChainTrace empty_state block_state) :
    env_contracts block_state randao_addr = Some (contract : WeakContract) ->
    exists (cstate : State),
      contract_state block_state randao_addr = Some cstate /\
      forall (campaignID : CampaignId) (campaign : Campaign),
        FMap.find campaignID cstate.(campaigns) = Some campaign ->
        Nat.eqb campaign.(commitNum) 0 = true ->
        campaign.(random) = 0.
  Proof.
    intros.
    specialize (not_enough_commit block_state randao_addr trace H). intro L.
    destruct L as [cstate L]. destruct L as [call_info L]. destruct L as [deploy_info L].
    specialize L as [L1 [L2 [L3 L4]]]. exists cstate. split; auto.
    apply L4.
  Qed.
  
  (* 
    3-1 
    If the participant fails to reveal s in the second phase, 
    then the m ETH sent in the first phase will be confiscated without providing a return.
  *)
  Theorem confiscate_deposit
    (chain : Chain) (ctx : ContractCallContext) (state : State) (campaignID : CampaignId) :
    forall (c : Campaign) (p : Participant), 
      FMap.find campaignID state.(campaigns) = Some c ->
      FMap.find ctx.(ctx_from) c.(participants) = Some p ->
      Z.of_nat c.(revealsNum) >? 0 = true -> 
      p.(revealed) = false ->
      getMyBounty_body chain ctx state campaignID = Err default_error.
  Proof.
    intros. unfold getMyBounty_body. rewrite H. cbn. rewrite H0. cbn.
    destruct (bountyPhase chain c.(bnum)); cbn; try auto.
    destruct (beFalse p.(rewarded)); cbn; try auto.
    rewrite H1. rewrite H2. auto.
  Qed.

  (*
    3.2 
    If one or more s isn't revealed in the second phase, 
    RNG at this block height will fail. 
    Confiscated ETHs will be divided equally and send to other participants who revealed s at the second phase. 
    The fees paid by other contracts will be refunded. 
  *)

  (* 十分な balance が存在する *)
  
  (* 報酬を受け取れて, まだ報酬を受け取っていない参加者数. 証明のため, FMap.elementsで実装 *)
  Definition unrewardedNum (campaign : Campaign) : nat :=
    List.length (List.filter (fun '(_ ,p) => andb (revealed p) (negb (rewarded p))) (FMap.elements (campaign.(participants)))).

  (* 誰もrevealしない場合の, まだ報酬を受け取っていない参加者数. 証明のため, FMap.elementsで実装 *)
  Definition unrewarded_participantsNum (campaign : Campaign) : nat :=
    List.length (List.filter (fun '(_ ,p) => negb (rewarded p)) (FMap.elements (campaign.(participants)))).

  (* RNG失敗時の返金されていない消費者の報酬の合計. 返金済みは 0 *)
  Definition refundsSum (campaign : Campaign) : Z :=
    sumZ (fun c => c.(bountypot)) (FMap.values (campaign.(consumers))).

  Definition campaign_return (chain : Chain) (c : Campaign) : Z :=
    if (bountyPhase chain c.(bnum)) then
       Z.of_nat c.(commitNum) * Z.of_nat c.(deposit) + c.(bountypot_campaign)
    else      
      if (Z.of_nat c.(revealsNum) >? 0)
        then (
          if (Z.of_nat c.(commitNum) >? Z.of_nat c.(revealsNum)) then 
            let fail_reward :=
              (Z.of_nat c.(commitNum) - Z.of_nat c.(revealsNum)) * Z.of_nat c.(deposit) / Z.of_nat c.(revealsNum) + Z.of_nat c.(deposit) in
            fail_reward * Z.of_nat (unrewardedNum c) + refundsSum c
          else 
            let success_reward := c.(bountypot_campaign) / Z.of_nat c.(revealsNum) + Z.of_nat c.(deposit) in
            success_reward * Z.of_nat (unrewardedNum c)
        )
      else
        Z.of_nat (unrewarded_participantsNum c) * Z.of_nat c.(deposit) + refundsSum c.

  Definition total_returns (chain : Chain) (cstate : State) : Z :=
    sumZ (campaign_return chain) (FMap.values cstate.(campaigns)).

  (* 補題たち *)
  (* total_returns_devide_prev, total_returns_devide_new の補題 *)
  Lemma total_returns_perm_fmap chain campaignID c (m m' : FMap CampaignId Campaign) :
    Permutation (FMap.elements m) ((campaignID, c) :: FMap.elements m') ->
    sumZ (campaign_return chain) (FMap.values m) = sumZ (campaign_return chain) (c :: FMap.values m').
  Proof.
    intros perm.
    assert (A : Permutation (map snd (FMap.elements m)) (map snd ((campaignID, c) :: FMap.elements m'))). apply (Permutation_map). apply perm.
    rewrite <- (sumZ_permutation A). auto.
  Qed.

  (* incoming call での補題 *)
  Lemma total_returns_devide_prev chain state campaignID c :
    FMap.find campaignID (campaigns state) = Some c ->
    total_returns chain state = campaign_return chain c + sumZ (campaign_return chain) (FMap.values (FMap.remove campaignID state.(campaigns))).
  Proof.
    unfold total_returns. intros.
    assert (A: Permutation (FMap.elements (campaigns state)) (FMap.elements (FMap.add campaignID c (FMap.remove campaignID (campaigns state))))).
    { rewrite FMap.add_remove. rewrite (FMap.add_id campaignID c); auto. }
    specialize (FMap.elements_add campaignID c (FMap.remove campaignID (campaigns state))). rewrite FMap.find_remove. intro L.
    assert (A2: Permutation (FMap.elements (campaigns state)) ((campaignID, c) :: FMap.elements (FMap.remove campaignID (campaigns state)))).
    { apply Permutation_trans with (FMap.elements (FMap.add campaignID c (FMap.remove campaignID (campaigns state)))). apply A. apply L. auto. }
    rewrite (total_returns_perm_fmap chain campaignID c (campaigns state) (FMap.remove campaignID (campaigns state))); auto.
  Qed.

  (* incoming call での補題 *)
  Lemma total_returns_devide_new chain state campaignID c {numCampaigns founder} :
    let new_state :=
      {|
        numCampaigns := numCampaigns;
        campaigns := FMap.add campaignID c (campaigns state);
        founder := founder
      |} in
    total_returns chain new_state = campaign_return chain c + sumZ (campaign_return chain) (FMap.values (FMap.remove campaignID state.(campaigns))).
  Proof.
    unfold total_returns. cbn.
    rewrite <- FMap.add_remove. 
    specialize (FMap.elements_add campaignID c (FMap.remove campaignID (campaigns state))). rewrite FMap.find_remove; intro L.
    rewrite (total_returns_perm_fmap chain campaignID c (FMap.add campaignID c (FMap.remove campaignID (campaigns state))) (FMap.remove campaignID (campaigns state))).
    auto. apply L. auto.
  Qed.

  (* AddBlock 本体で証明しても良いかも *) 
  Lemma campaign_return_le old_chain new_chain campaign :
    refundsSum campaign <= campaign.(bountypot_campaign) -> (* subgoal で入手予定 *)
    Nat.lt old_chain.(chain_height) new_chain.(chain_height) -> (* AddBlockFacts で入手予定 *)
    Nat.le (unrewardedNum campaign) campaign.(revealsNum) -> 
    Nat.le (unrewarded_participantsNum campaign) campaign.(commitNum) -> 
    Nat.le campaign.(revealsNum) campaign.(commitNum) ->
    Z.of_nat campaign.(deposit) <=? 0 = false -> (* morethanZero *)
    0 <= bountypot_campaign campaign -> (* subgoal *)
    campaign_return new_chain campaign <= campaign_return old_chain campaign.
  Proof.
    intros. unfold campaign_return.
    apply inj_le in H1. apply inj_le in H2. apply inj_le in H3. apply Z.leb_gt in H4.
    destruct (bountyPhase new_chain (bnum campaign)) eqn:Bn.
    - (* bountyPhase new_chain _ = true *)
      destruct (bountyPhase old_chain (bnum campaign)) eqn:Bo; try lia.
      (* 矛盾を導く *)
      unfold bountyPhase in *. lia.
    - (* bountyPhase new_chain _ = false *)
      destruct (bountyPhase old_chain (bnum campaign)) eqn:Bo; try lia.
      (* bountyPhase old_chain _ = true *)
      destruct (Z.of_nat (revealsNum campaign) >? 0) eqn:Breveal.
      + destruct (Z.of_nat (commitNum campaign) >? Z.of_nat (revealsNum campaign)) eqn:Bfail.
        * (* RNG fail in new_chain *) 
          apply Z.add_le_mono; try lia.                    
          rewrite Z.mul_add_distr_r.
          rewrite Z.mul_sub_distr_r.
          rewrite Z.mul_comm with (Z.of_nat (revealsNum campaign)) (Z.of_nat (deposit campaign)).
          rewrite <- Z.add_opp_r.
          rewrite <- Z.mul_opp_l.
          rewrite Z.div_add; try lia. rewrite Z.add_opp_r.
          rewrite Z.mul_sub_distr_r.
          rewrite Z.sub_add.
          apply Z.gtb_lt in Breveal.
          specialize (Z.mul_div_le (Z.of_nat (commitNum campaign) * Z.of_nat (deposit campaign)) (Z.of_nat (revealsNum campaign)) Breveal) as M.
          intros. 
          rewrite Z.mul_comm in M.
          apply Z.le_trans with (Z.of_nat (commitNum campaign) * Z.of_nat (deposit campaign) / Z.of_nat (revealsNum campaign) * Z.of_nat (revealsNum campaign)).
          2: apply M.
          apply Z.mul_le_mono_nonneg_l.
          apply Z.div_pos; lia. apply H1.
        * (* RNG success *)
          rewrite Z.mul_add_distr_r. rewrite Z.add_comm.
          apply Z.add_le_mono.
          -- rewrite Z.mul_comm. apply Z.mul_le_mono_nonneg_r; lia.
          -- apply Z.le_trans with (Z.of_nat (revealsNum campaign) * (bountypot_campaign campaign / Z.of_nat (revealsNum campaign))).
            2: apply Z.mul_div_le; lia.
            rewrite Z.mul_comm. apply Z.mul_le_mono_nonneg_r. apply Z.div_pos; lia.
            apply H1.
      + (* revealsNum = 0 *)
        apply Z.add_le_mono; try lia. apply Z.mul_le_mono_nonneg_r; lia.
  Qed.

  Definition Participant_eq_dec : forall x y : Participant, {x = y} + {x <> y}.
  Proof.
    decide equality. 
    - decide equality.
    - decide equality.
    - decide equality.
      + decide equality.
      + decide equality.
    - apply Z.eq_dec.
    - apply Z.eq_dec.
  Defined.

  Definition Participants_eq_dec : forall x y : (Address * Participant), {x = y} + {x <> y}.
  Proof.
    decide equality. 
    - apply Participant_eq_dec. 
    - apply address_eqdec.
  Defined.

  (* remove_FMap2list で使用 *)
  Lemma Permutaiton_remove : forall [A : Type] (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l l1 : list A),
    Permutation l l1 -> Permutation (remove eq_dec x l) (remove eq_dec x l1).
  Proof.
    intros A eq_dec x l. induction l as [|h l' IHl'].
    - intros. apply list.Permutation_nil_l in H. subst; auto.
    - intros. simpl.
      destruct (eq_dec x h) eqn:B.
      + apply list.Permutation_cons_inv_l in H as [k1 [k2 [IH1 IH2]]].
        rewrite e in *. rewrite IH1. rewrite remove_app. simpl. rewrite B. rewrite <- remove_app.
        apply IHl'. apply IH2.
      + apply list.Permutation_cons_inv_l in H as [k1 [k2 [IH1 IH2]]]. rewrite IH1.
        rewrite remove_app. simpl. rewrite B. apply Permutation_trans with (h :: remove eq_dec x k2 ++ remove eq_dec x k1).
        apply perm_skip. rewrite <- remove_app. apply IHl'. apply Permutation_trans with (k1 ++ k2); auto. apply Permutation_app_comm.
        apply Permutation_cons_app. apply Permutation_app_comm.
  Qed.

  (* incoming_call の多くのブランチで使用 *)
  Lemma filter_remove : forall [A : Type] (eq_dec : forall x y : A, {x = y} + {x <> y}) (f : A -> bool) (x : A) (l : list A),
    filter f (remove eq_dec x l) = remove eq_dec x (filter f l).
  Proof.
    intros. induction l as [|h l' IHl'].
    - auto.
    - simpl. destruct (eq_dec x h) eqn:B. 
      + destruct (f h) eqn:B1.
        * simpl. rewrite B. auto.
        * apply IHl'.
      + simpl. destruct (f h) eqn:B1.
        * simpl. destruct (eq_dec x h) as [H | H]. contradiction. rewrite IHl'. auto.
        * apply IHl'.
  Qed.   

  (* l内に既存の時 *)
  Lemma length_remove_NoDup : forall [A : Type] (eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A),
    NoDup l ->
    In x l  ->
    Z.of_nat (length (remove eq_dec x l)) =  Z.of_nat (length l) - 1.
  Proof.
    intros A eq_dec x l. induction l as [|h l' IHl'].
    - simpl. auto.
    - intros.
      apply NoDup_cons_iff in H as [H H1]. simpl.
      destruct (eq_dec x h) as [Heq|Hneq].
      + rewrite Heq in *. rewrite notin_remove by apply H. lia.
      + simpl. rewrite Nat2Z.inj_succ. rewrite IHl'; auto. lia.
        simpl in H0. destruct H0 as [H0|H0]; auto.
        rewrite H0 in Hneq. contradiction.
  Qed. 

    (* Listモジュールにありそう? remove_FMap2listでsimplしないために使用 *)
  Lemma remove_ne : forall [A : Type] (eq_dec : forall x y : A, {x = y} + {x <> y}) (x y : A) (l : list A),
    x <> y -> remove eq_dec x (y :: l) = y :: (remove eq_dec x l).
  Proof.
    intros A eq_dec x y l H. simpl.
    destruct (eq_dec x y) as [Heq | Hneq]; auto. contradiction.
  Qed.

  (* 既存の時の補題. k の等号でdestruct するために, 多相型での証明は断念 *)
  Lemma remove_FMap2list : forall (k : Address) (v : Participant) (m : FMap Address Participant),
    FMap.find k m = Some v ->
    Permutation (FMap.elements (FMap.remove k m)) (List.remove Participants_eq_dec (k, v) (FMap.elements m)).
  Proof.
    intros k v.
    apply (FMap.ind (fun m => FMap.find k m = Some v -> 
      Permutation (FMap.elements (FMap.remove k m)) (remove Participants_eq_dec (k, v) (FMap.elements m)))).
    - (* basecase *)
      rewrite FMap.find_empty. auto.
    - (* ind case *)
      intros.
      destruct (address_eqb k k0) eqn:B. 
      + destruct (address_eqb_spec k k0) as [B'|]; try discriminate B. rewrite <- B' in *.
        rewrite FMap.remove_add by apply H.
        apply Permutation_trans with (remove Participants_eq_dec (k, v) ((k, v0) :: FMap.elements m)).
        * rewrite FMap.find_add in H1. inversion H1. rewrite remove_cons.
          rewrite notin_remove; auto. apply (FMap.not_In_elements). auto.
        * apply Permutaiton_remove. rewrite FMap.elements_add; auto.
      + destruct (address_eqb_spec k k0) as [|B']; try discriminate B. 
        rewrite FMap.find_add_ne in H1; auto.
        rewrite fin_maps.delete_insert_ne; auto.
        rewrite FMap.elements_add.
        apply Permutation_trans with (remove Participants_eq_dec (k, v) ((k0, v0) :: FMap.elements m)).
        * destruct (Participants_eq_dec (k, v) (k0, v0)) as [Heq | Hneq'].
          { inversion Heq. apply B' in H3. auto. }
          { rewrite remove_ne; auto. } (* Participants_eq_dec を simpl したくないから, lemma を作った *)  
        * apply Permutaiton_remove. apply Permutation_sym. apply FMap.elements_add. auto.
        * rewrite FMap.find_remove_ne by apply B'; auto.
  Qed.

  (* refundsSum_devide 用 *)
  Lemma refundsSum_perm_fmap consumer_addr c (m m' : FMap Address Consumer ) :
    Permutation (FMap.elements m) ((consumer_addr, c) :: FMap.elements m') ->
    sumZ (fun c => c.(bountypot)) (FMap.values m) = sumZ (fun c => c.(bountypot)) (c :: FMap.values m').
  Proof.
    intros perm.
    assert (A : Permutation (map snd (FMap.elements m)) (map snd ((consumer_addr, c) :: FMap.elements m'))). apply (Permutation_map). apply perm.
    rewrite <- (sumZ_permutation A). auto.
  Qed.

  (* consumers が変わるブランチ *)
  Lemma refundsSum_devide_prev campaign consumer_addr c:
    FMap.find consumer_addr campaign.(consumers) = Some c ->
    refundsSum campaign = c.(bountypot) + sumZ (fun c => c.(bountypot)) (FMap.values (FMap.remove consumer_addr campaign.(consumers))).
  Proof.
    unfold refundsSum. intros.
    assert (A: Permutation (FMap.elements (consumers campaign)) (FMap.elements (FMap.add consumer_addr c (FMap.remove consumer_addr (consumers campaign))))).
    { rewrite FMap.add_remove. rewrite (FMap.add_id consumer_addr c); auto. }
    specialize (FMap.elements_add consumer_addr c (FMap.remove consumer_addr (consumers campaign))). rewrite FMap.find_remove. intro L.
    assert (A2: Permutation (FMap.elements (consumers campaign)) ((consumer_addr, c) :: FMap.elements (FMap.remove consumer_addr (consumers campaign)))).
    { apply Permutation_trans with (FMap.elements (FMap.add consumer_addr c (FMap.remove consumer_addr (consumers campaign)))). apply A. apply L. auto. }
    rewrite (refundsSum_perm_fmap consumer_addr c (consumers campaign) (FMap.remove consumer_addr (consumers campaign))); auto.
  Qed.

  (* consumers が変わるブランチ *)
  Lemma refundsSum_devide_new consumers consumer_addr c 
    { bnum deposit commitBalkline commitDeadline random settled bountypot_campaign commitNum revealsNum participants commitments } :
    let new_campaign := {|
      bnum := bnum;
      deposit := deposit;
      commitBalkline := commitBalkline;
      commitDeadline := commitDeadline;
      random := random;
      settled := settled;
      bountypot_campaign := bountypot_campaign;
      commitNum := commitNum;
      revealsNum := revealsNum;
      consumers := FMap.add consumer_addr c consumers;
      participants := participants;
      commitments := commitments;
    |} in
    refundsSum new_campaign = c.(bountypot) + sumZ (fun c => c.(bountypot)) (FMap.values (FMap.remove consumer_addr consumers)).
  Proof.
    unfold refundsSum. cbn.
    rewrite <- FMap.add_remove. 
    specialize (FMap.elements_add consumer_addr c (FMap.remove consumer_addr consumers)). rewrite FMap.find_remove; intro L.
    rewrite (refundsSum_perm_fmap consumer_addr c (FMap.add consumer_addr c (FMap.remove consumer_addr consumers)) (FMap.remove consumer_addr consumers)).
    auto. apply L. auto.
  Qed.

  (* getMyBounty の本体の証明で使用 *)
  Lemma unrewardedNum_rewarded campaign p_addr p_prev p_new 
    { bnum deposit commitBalkline commitDeadline random settled bountypot_campaign commitNum revealsNum consumers commitments } :
    FMap.find p_addr campaign.(participants) = Some p_prev ->
    revealed p_prev = true ->
    rewarded p_prev = false ->
    andb (revealed p_new) (negb (rewarded p_new)) = false ->
    let new_campaign := {|
      bnum := bnum;
      deposit := deposit;
      commitBalkline := commitBalkline;
      commitDeadline := commitDeadline;
      random := random;
      settled := settled;
      bountypot_campaign := bountypot_campaign;
      commitNum := commitNum;
      revealsNum := revealsNum;
      consumers := consumers;
      participants := FMap.add p_addr p_new campaign.(participants);
      commitments := commitments;
    |} in
    Z.of_nat (unrewardedNum new_campaign) = Z.of_nat (unrewardedNum campaign) - 1.
  Proof.
    intros. unfold unrewardedNum. unfold new_campaign. cbn. 
    replace (Z.of_nat (length (filter (fun '(_, p) => (revealed p && negb (rewarded p))%bool) 
                (FMap.elements (FMap.add p_addr p_new (participants campaign))))))
      with (Z.of_nat (length (filter (fun '(_, p) => (revealed p && negb (rewarded p))%bool)
                ((p_addr , p_new) :: remove Participants_eq_dec (p_addr , p_prev) (FMap.elements (participants campaign)))))).
    {
      (* goal *)
      simpl. rewrite H2. rewrite filter_remove. 
      rewrite length_remove_NoDup.
      - lia. 
      - apply List.NoDup_filter. apply FMap.NoDup_elements.
      - apply FMap.In_elements in H.
        apply filter_In. rewrite H0, H1. split; auto.
    }
    {
      (* replace の証明 *)
      apply f_equal. apply Permutation_length. apply Permutation_filter. 
      rewrite FMap.elements_add_existing by apply H.
      apply perm_skip. apply Permutation_sym. apply remove_FMap2list; auto.
    }
  Qed.

  (* getMyBounty の本体の証明で使用 *)
  Lemma unrewarded_participantsNum_rewarded campaign p_addr p_prev p_new 
    { bnum deposit commitBalkline commitDeadline random settled bountypot_campaign commitNum revealsNum consumers commitments } :
    FMap.find p_addr campaign.(participants) = Some p_prev ->
    rewarded p_prev = false ->
    (rewarded p_new) = true ->
    let new_campaign := {|
      bnum := bnum;
      deposit := deposit;
      commitBalkline := commitBalkline;
      commitDeadline := commitDeadline;
      random := random;
      settled := settled;
      bountypot_campaign := bountypot_campaign;
      commitNum := commitNum;
      revealsNum := revealsNum;
      consumers := consumers;
      participants := FMap.add p_addr p_new campaign.(participants);
      commitments := commitments;
    |} in
    Z.of_nat (unrewarded_participantsNum new_campaign) = Z.of_nat (unrewarded_participantsNum campaign) - 1.
  Proof.
    intros. unfold unrewarded_participantsNum. unfold new_campaign. cbn. 
    replace (Z.of_nat (length (filter (fun '(_, p) => negb (rewarded p)) (FMap.elements (FMap.add p_addr p_new (participants campaign))))))
      with (Z.of_nat (length (filter (fun '(_, p) => negb (rewarded p))
                ((p_addr , p_new) :: remove Participants_eq_dec (p_addr , p_prev) (FMap.elements (participants campaign)))))).
    {
      (* goal *)
      simpl. rewrite H1. cbn. rewrite filter_remove. 
      rewrite length_remove_NoDup.
      - lia. 
      - apply List.NoDup_filter. apply FMap.NoDup_elements.
      - apply FMap.In_elements in H.
        apply filter_In. rewrite H0. split; auto.
    }
    {
      (* replace の証明 *)
      apply f_equal. apply Permutation_length. apply Permutation_filter. 
      rewrite FMap.elements_add_existing by apply H.
      apply perm_skip. apply Permutation_sym. apply remove_FMap2list; auto.
    }
  Qed.

  (* revealsNum <= commitNum - length filter (fun p => negb revealed p) m, unrewardedNum, unrewardedNum_participant の証明で使用 *)
  Lemma replace_length_filter_add_existing (v_prev v_new : Participant ) (k : Address) (m : FMap Address Participant) (f : Address * Participant -> bool) :
    FMap.find k m = Some v_prev ->
    (Z.of_nat (length (filter f (FMap.elements (FMap.add k v_new m)))))
      = (Z.of_nat (length (filter f ((k , v_new) :: remove Participants_eq_dec (k, v_prev) (FMap.elements m))))).
  Proof. intros.
    apply f_equal. apply Permutation_length. apply Permutation_filter. 
    rewrite FMap.elements_add_existing by apply H.
    apply perm_skip. apply remove_FMap2list; auto.
  Qed.

  Lemma replace_length_filter_add_notin (v_new : Participant ) (k : Address) (m : FMap Address Participant) (f : Address * Participant -> bool) :
    FMap.find k m = None ->
    (Z.of_nat (length (filter f (FMap.elements (FMap.add k v_new m)))))
      = (Z.of_nat (length (filter f ((k , v_new) :: remove Participants_eq_dec (k, v_new) (FMap.elements m))))). (* 最後のv_newはダミー *)
  Proof. intros.
    apply f_equal. apply Permutation_length. apply Permutation_filter. 
    rewrite notin_remove; auto. 
    rewrite FMap.elements_add; auto.
    apply FMap.not_In_elements; auto.
  Qed.

  Lemma new_campaignID_fresh_existing (ctx : ContractCallContext) (prev_state : State) (campaignID : CampaignId) (campaign new_campaign : Campaign) :
    FMap.find campaignID (campaigns prev_state) = Some campaign -> 
    (forall new_campaignID : CampaignId,
        Nat.le (FMap.size (campaigns prev_state) + 1) new_campaignID -> 
        FMap.find new_campaignID (campaigns prev_state) = None) -> 
    forall new_campaignID : CampaignId,
      Nat.le (FMap.size (FMap.add campaignID new_campaign (campaigns prev_state)) + 1) new_campaignID -> 
      FMap.find new_campaignID (FMap.add campaignID new_campaign (campaigns prev_state)) = None.
  Proof.
    intros Hr1 IH. 
    rewrite FMap.size_add_existing; auto. 
    + intros. destruct (Nat.eqb new_campaignID campaignID) eqn:B.  
      * apply Nat.eqb_eq in B. rewrite B in *. rewrite (IH campaignID H) in Hr1. discriminate Hr1.
      * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
        rewrite FMap.find_add_ne by apply B. apply (IH new_campaignID H).
    + destruct (FMap.find campaignID (campaigns prev_state)) eqn:Hfind; auto. (* rewrite できなかった *)  
  Qed.

  Lemma enough_balance_withlemma block_state randao_addr (trace : ChainTrace empty_state block_state) :
    env_contracts block_state randao_addr = Some (contract : WeakContract) ->
    exists (cstate : State) (call_info : list (ContractCallInfo Msg)) (deploy_info : DeploymentInfo Setup),
      contract_state block_state randao_addr = Some cstate /\
      incoming_calls Msg trace randao_addr = Some call_info /\
      deployment_info _ trace randao_addr = Some deploy_info /\
      let chain := {| chain_height := block_state.(chain_height);
                      current_slot := block_state.(current_slot);
                      finalized_height := block_state.(finalized_height); |} in
      (* A *)
      (
        (
          forall (campaignID : CampaignId) (campaign : Campaign),
            FMap.find campaignID cstate.(campaigns) = Some campaign -> 
            (Z.of_nat campaign.(commitDeadline) <=? 0) = false /\         
            Z.of_nat campaign.(deposit) <=? 0 = false /\                   
            0 <= campaign.(bountypot_campaign) /\                            
            refundsSum campaign <= campaign.(bountypot_campaign) /\             
            Nat.le (unrewardedNum campaign) campaign.(revealsNum) /\            
            Nat.le (unrewarded_participantsNum campaign) campaign.(commitNum) /\ 
            Z.of_nat campaign.(revealsNum) =                                   
              Z.of_nat campaign.(commitNum) - Z.of_nat (List.length (List.filter (fun '(_ ,p) => negb (revealed p)) (FMap.elements (campaign.(participants))))) /\
            (
              forall (hs : Z) (b : bool), 
                FMap.find hs campaign.(commitments) = Some b -> b = true 
            ) /\              
            (
              forall (call_origin : Address) (call_from : Address) (call_amount : Amount),
                let ctx := {| ctx_origin := call_origin;
                              ctx_from := call_from;
                              ctx_contract_address := randao_addr;
                              ctx_contract_balance := env_account_balances block_state randao_addr;
                              ctx_amount := call_amount |} in         
                (
                  forall (consumer : Consumer), 
                    FMap.find ctx.(ctx_from) campaign.(consumers) = Some consumer ->
                    consumer.(consumer_addr) = ctx.(ctx_from) /\ 
                    0 <= consumer.(bountypot)                    
                ) /\
                (
                  forall (participant : Participant),
                    FMap.find ctx.(ctx_from) campaign.(participants) = Some participant ->
                    participant.(commitment) =? 0 = false                   
                )
            )
        ) /\ 
        (
          forall (new_campaignID : CampaignId),
            Nat.le (Nat.add (FMap.size (campaigns cstate)) 1) new_campaignID ->
            FMap.find new_campaignID cstate.(campaigns) = None 
        )
      ) /\
      (* B *)
      total_returns chain cstate <= (env_account_balances block_state randao_addr) - (sumZ act_body_amount (outgoing_acts block_state randao_addr)).
  Proof.
    contract_induction; intros.
    - (* AddBlock *)
      instantiate (AddBlockFacts := fun old_height _ _ new_height _ _ => Nat.lt old_height new_height); unfold AddBlockFacts in facts.
      split.
      {
        (* A *)
        apply IH.
      }
      destruct IH as [L IH].
      unfold total_returns in *. cbn in *. rewrite Z.sub_0_r in *. 
      apply Z.le_trans with (sumZ (campaign_return {| chain_height := old_chain_height; current_slot := old_cur_slot; finalized_height := old_fin_height |})
        (FMap.values (campaigns state))); auto.
      apply sumZ_le. intros. unfold FMap.values in H. apply in_map_iff in H as [[campaignID campaign] [H H0]].
      simpl in H. rewrite <- H in *.
      apply FMap.In_elements in H0. 
      apply L in H0 as [L1 [L2 [L3 [L4 [L5 [L6 [L7 _]]]]]]].
      assert (L7': Z.of_nat (revealsNum campaign) <= Z.of_nat (commitNum campaign)).
        { rewrite L7. lia. }
      apply campaign_return_le; auto; try lia.
    - (* Deploy *)
      instantiate (DeployFacts := fun _ _ctx => 0 <= _ctx.(ctx_amount)); unfold DeployFacts in facts.
      inversion init_some. cbn. split.
      {
        (* A *)
        split.
        - intros campaignID campaign. rewrite FMap.find_empty. discriminate. (* campaigns は空 *)
        - intros. apply FMap.find_empty. 
      }
      unfold total_returns. cbn. unfold FMap.values. rewrite FMap.elements_empty. cbn. lia.
    - (* outgoing call *)
        cbn in IH. split. apply IH. lia. 
    - (* non recursive incoming call *) 
      instantiate (CallFacts := fun _ _ctx _ _ _ => 0 <= _ctx.(ctx_amount)); 
      unfold CallFacts in facts.
      destruct msg as [msg|]; simpl in receive_some; try discriminate receive_some.
      destruct msg eqn:MSG; cbn in receive_some. 
      + (* numCampaigns *)
        inversion receive_some; cbn; rewrite H0 in *; split. apply IH. lia. 
      + (* campaigns *)
        destruct (result_of_option (FMap.find c (campaigns prev_state)) default_error); inversion receive_some.
        rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* founder *)
        inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* getCommitment *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some. 
        destruct (result_of_option (FMap.find (ctx_from ctx) (participants c0)) default_error) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* shaCommit *)
        unfold shaCommit_body in receive_some. inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* follow *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr2; cbn in receive_some.
        { 
          (* 二重 follow はエラー *)
          destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
          destruct (blankAddress (consumer_addr c1)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
          unfold blankAddress in Hr4.
          specialize IH as [[IH _] _]; auto.
          specialize (IH c c0 Hr1) as [_ [_ [_ [_ [_ [_ [_ [_ IH]]]]]]]]. 
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [IH _]. 
          specialize (IH c1 Hr2) as [IH _]. cbn in IH.
          rewrite IH in Hr4. rewrite null_address_not_valid in Hr4. discriminate Hr4.
        }
        destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        unfold blankAddress in receive_some. rewrite address_eq_refl in receive_some. cbn in receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers in receive_some; cbn in receive_some.
        rewrite FMap.add_add in receive_some. inversion receive_some. cbn.    
        split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H; cbn in *. 
              specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; try apply IH; try lia; auto.
              * rewrite refundsSum_devide_new. unfold refundsSum in L4. cbn.
                rewrite <- fin_maps.delete_notin with (consumers c0) (ctx_from ctx) in L4; auto. lia.
              *  
                specialize (L9 call_origin call_from call_amount) as [L9 _].
                specialize (L9 consumer).
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _].
                specialize (L9 consumer).
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * apply (L9 call_origin call_from call_amount); auto. 
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
          - (* new_campaignID is fresh *)
            specialize IH as [_ IH]. 
            apply (new_campaignID_fresh_existing ctx prev_state c c0); auto.         
        }
        (* B *)
        specialize IH as [[L _] IH].
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
        rewrite total_returns_devide_new.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *. 
        destruct (bountyPhase {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} (bnum _)) eqn:B; try lia.
        specialize (L c c0 Hr1) as [L _].
        destruct (contraPhase_follow_bounty chain c0); auto.
      + (* commit *) 
        destruct (notBeBlank z) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkDeposit ctx (deposit c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkCommitPhase chain (bnum c0) (commitBalkline c0) (commitDeadline c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        {
          (* 二重 commit *)
          destruct (beBlank (commitment p)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          specialize IH as [[IH _] _].
          specialize (IH c c0 Hr2) as [_ [_ [_ [_ [_ [_ [_ [_ IH]]]]]]]].  
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [_ IH].
          unfold beBlank in Hr6. rewrite IH in Hr6; auto. discriminate Hr6.
        }
        destruct (FMap.find z (commitments c0)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
        {
          (* commitments が存在 *)
          specialize IH as [[IH _] _].
          specialize (IH c c0 Hr2) as [_ [_ [_ [_ [_ [_ [_ [IH _]]]]]]]].
          specialize (IH z b). rewrite IH in receive_some; auto. cbn in receive_some; discriminate receive_some.
        }
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_commitments, set_Campaign_commitments,
          setter_from_getter_Campaign_commitNum, set_Campaign_commitNum, setter_from_getter_Campaign_participants, set_Campaign_participants in receive_some; cbn in receive_some.
        inversion receive_some; cbn. split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H; cbn in *. 
              specialize (IH c c0 Hr2) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; try apply IH; try lia; auto.
              * (* participant は追加されたが, revealed = false より変化無し *)
                unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_notin {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |}); auto.               
                simpl.
                rewrite filter_remove. apply Nat2Z.inj_le. rewrite notin_remove.
                -- unfold unrewardedNum in L5. lia.
                -- intro. apply filter_In in H2 as [contra _].
                  assert (A: ~ In (ctx_from ctx, {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |})
                  (FMap.elements (participants c0))).
                  apply FMap.not_In_elements; auto. contradiction.               
              * (* 参加者が追加されたため, unrewarded_participantsNum も増加 *)
                unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_notin); auto.  
                simpl. rewrite filter_remove. rewrite notin_remove.
                -- unfold unrewarded_participantsNum in L6. lia.
                -- intro. apply filter_In in H2 as [contra _].
                  assert (A: ~ In (ctx_from ctx, {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |})
                  (FMap.elements (participants c0))).
                  apply FMap.not_In_elements; auto. contradiction.
              * (* 以前はparticipant は存在しない *)
                rewrite replace_length_filter_add_notin; auto.
                simpl. rewrite filter_remove. rewrite notin_remove. lia.
                intro. apply filter_In in H2 as [contra _].
                assert (A: ~ In (ctx_from ctx, {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |})
                (FMap.elements (participants c0))).
                apply FMap.not_In_elements; auto. contradiction.
              * intros. destruct (Z.eqb hs z) eqn:B1.
                -- apply Z.eqb_eq in B1. rewrite B1 in *. rewrite FMap.find_add in H2. inversion H2. auto.
                -- apply Z.eqb_neq in B1. rewrite FMap.find_add_ne in H2; auto. 
                  apply (L8 hs); auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
              * intros. 
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. 
                  unfold notBeBlank in Hr1. auto.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto.
                  specialize (L9 call_origin call_from call_amount) as [_ L9].
                  apply (L9 participant); auto.
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              repeat (rewrite FMap.find_add_ne in H; auto). 
              apply (IH campaignID campaign H).
          - (* new_campaignID is fresh *)
            specialize IH as [_ IH]. intros.           
            rewrite FMap.size_add_existing in H; try (rewrite FMap.find_add; auto). 
            rewrite FMap.size_add_existing in H; try (rewrite FMap.find_add; auto).
            rewrite FMap.size_add_existing in H; auto. 
            + specialize (IH new_campaignID H). 
              destruct (Nat.eqb new_campaignID c) eqn:B. 
              * apply Nat.eqb_eq in B. rewrite B in IH. rewrite Hr2 in IH. discriminate IH. 
              * apply Nat.eqb_neq in B. repeat (rewrite FMap.find_add_ne; auto).
            + destruct (FMap.find c (campaigns _)) eqn:contra; auto.
        }
        (* B *)
        specialize IH as [[L _] IH]. repeat rewrite FMap.add_add.
        rewrite total_returns_devide_new. 
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr2) in IH.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *.
        destruct (bountyPhase {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} (bnum _)) eqn:B; try lia.
        * unfold checkDeposit in Hr3. apply Bool.negb_false_iff in Hr3. apply Z.eqb_eq in Hr3. 
          rewrite Hr3 in *. lia.
        * specialize (L c c0 Hr2) as [L _].
          destruct (contraPhase_commit_bounty chain c0); auto.
      + (* reveal *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkRevealPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkSercret z (commitment p)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (revealed p) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants,
          setter_from_getter_Participant_revealed, set_Participant_revealed, setter_from_getter_Participant_secret, set_Participant_secret in receive_some; cbn in receive_some.
        inversion receive_some. cbn. split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H; cbn in *. 
              specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; try auto; try lia.
              * unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_existing p); auto.        
                simpl. destruct (rewarded _) eqn:B1; cbn.
                -- rewrite filter_remove. rewrite notin_remove.
                  ++ unfold unrewardedNum in L5. lia.
                  ++ intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto. (* rewarded は矛盾 *)
                -- rewrite filter_remove. rewrite notin_remove.
                  ++ unfold unrewardedNum in L5. lia.
                  ++ intro. apply filter_In in H2 as [_ contra]. rewrite Hr5 in contra. auto.
              * unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_existing p); auto.  
                simpl. destruct (rewarded _) eqn:B1; cbn.
                -- rewrite filter_remove. rewrite notin_remove.
                  ++ unfold unrewarded_participantsNum in L6. lia.
                  ++ intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto. (* rewarded は矛盾 *)
                -- rewrite filter_remove. rewrite Nat2Z.inj_succ.
                  rewrite length_remove_NoDup.
                  ++ unfold unrewarded_participantsNum in L6. lia.
                  ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                  ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite B1. auto. 
              * rewrite (replace_length_filter_add_existing p); auto. 
                simpl. rewrite filter_remove. 
                rewrite length_remove_NoDup.
                -- lia. 
                -- apply List.NoDup_filter. apply FMap.NoDup_elements.
                -- apply FMap.In_elements in Hr2.
                  apply filter_In. split; auto. rewrite Hr5. auto. 
              * apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _].
                apply L9; auto.
              * intros. specialize (L9 call_origin call_from call_amount) as [_ L9].
                destruct (address_eqb call_from (ctx_from ctx)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. simpl. 
                  destruct (rewarded _) eqn:B2; try discriminate. intros.
                  apply (L9 p Hr2). auto. 
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto.
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
          - (* new_campaignID is fresh *)
            specialize IH as [_ IH]. 
            apply (new_campaignID_fresh_existing ctx prev_state c c0); auto.  
        }
          (* B *)
        specialize IH as [_ IH]. rewrite total_returns_devide_new. 
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *.
        destruct (bountyPhase {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} (bnum _)) eqn:B; try lia.
        destruct (contraPhase_reveal_bounty chain c0); auto.        
      + (* getMyBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (rewarded p) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        split.
        {
          (* A *)
          destruct IH as [IH _].
          destruct (Z.of_nat (revealsNum c0) >? 0) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
          - destruct (revealed p) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
            unfold returnReward in receive_some. cbn in receive_some.
            unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
              ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some. 
            inversion receive_some. cbn. split; intros.
            + specialize IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
              * apply Nat.eqb_eq in B. rewrite B in *.
                rewrite FMap.find_add in H. inversion H. cbn in *. 
                specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
                repeat split; auto; try lia.
                -- unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                  rewrite (replace_length_filter_add_existing p); auto.            
                  simpl. rewrite Bool.andb_false_r.
                  rewrite filter_remove. rewrite length_remove_NoDup.
                  ++ unfold unrewardedNum in L5. lia.
                  ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                  ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite Hr4, Hr6. auto. 
                -- unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                  rewrite (replace_length_filter_add_existing p); auto.   
                  simpl. rewrite filter_remove. rewrite length_remove_NoDup.
                  ++ unfold unrewarded_participantsNum in L6. lia.
                  ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                  ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite Hr4. auto. 
                -- rewrite (replace_length_filter_add_existing p); auto. 
                  destruct (revealed _) eqn:B2; try discriminate Hr6; cbn.
                  rewrite filter_remove. rewrite notin_remove. lia.
                  intro. apply filter_In in H2 as [_ contra]. rewrite B2 in contra. auto.
                -- apply L9; auto.
                -- specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
                -- intros. specialize (L9 call_origin call_from call_amount) as [_ L9]. 
                  destruct (address_eqb call_from (ctx_from ctx)) eqn:B1.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                    rewrite <- B' in *. rewrite FMap.find_add in H2. inversion H2. simpl. intros.
                    apply (L9 p); auto.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                    rewrite FMap.find_add_ne in H2; auto.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
            + specialize IH as [_ IH]. rewrite FMap.size_add_existing in H. intros.
              destruct (Nat.eqb new_campaignID c) eqn:B.  
              * apply Nat.eqb_eq in B. rewrite B in *. rewrite (IH c H) in Hr1. discriminate Hr1.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne by apply B. apply (IH new_campaignID H).
              * destruct (FMap.find c (campaigns prev_state)) eqn:Hfind; auto.
          - (* (revealsNum c0) = 0 *)
            unfold returnReward in receive_some. cbn in receive_some.
            unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
              ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some. 
            inversion receive_some. cbn. split; intros.
            + specialize IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
              * apply Nat.eqb_eq in B. rewrite B in *.
                rewrite FMap.find_add in H. inversion H. cbn in *. 
                specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
                repeat split; auto; try lia.
                -- (* new_participant は入らない. *)
                  unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                  rewrite (replace_length_filter_add_existing p); auto.
                  unfold unrewardedNum. cbn.
                  simpl. rewrite Bool.andb_false_r. 
                  destruct (andb (revealed p) (negb (rewarded p))) eqn:B1; cbn.
                  ++ (* p が入ってる. 本当は矛盾 *)
                    rewrite filter_remove. rewrite length_remove_NoDup.
                    ** unfold unrewardedNum in L5. lia.
                    ** apply List.NoDup_filter. apply FMap.NoDup_elements.
                    ** apply filter_In. split; auto. apply FMap.In_elements; auto. 
                  ++ (* p が入っていない *)
                  rewrite filter_remove. rewrite notin_remove.
                    ** unfold unrewardedNum in L5. lia.
                    ** intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto. 
                -- (* unrewarded が減る *) 
                    unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                    rewrite (replace_length_filter_add_existing p); auto.  
                    simpl. rewrite filter_remove. rewrite length_remove_NoDup.
                    ++ unfold unrewarded_participantsNum in L6. lia.
                    ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                    ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite Hr4. auto. 
                -- (* 変わらない. revealed p にかかわらず *) 
                  rewrite (replace_length_filter_add_existing p); auto.
                  destruct (revealed _) eqn:B1; cbn.
                  ++ rewrite filter_remove. rewrite notin_remove; auto. 
                    intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto.
                  ++ rewrite filter_remove. rewrite Nat2Z.inj_succ. rewrite length_remove_NoDup.
                    ** lia. 
                    ** apply List.NoDup_filter. apply FMap.NoDup_elements.
                    ** apply filter_In. split. apply FMap.In_elements; auto. rewrite B1. auto. 
                -- apply L9; auto.
                -- specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
                -- intros. specialize (L9 call_origin call_from call_amount) as [_ L9]. 
                  destruct (address_eqb call_from (ctx_from ctx)) eqn:B1.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                    rewrite <- B' in *. rewrite FMap.find_add in H2. inversion H2. simpl. intros.
                    apply (L9 p); auto.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                    rewrite FMap.find_add_ne in H2; auto.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
            + specialize IH as [_ IH]. rewrite FMap.size_add_existing in H. intros.
              destruct (Nat.eqb new_campaignID c) eqn:B.  
              * apply Nat.eqb_eq in B. rewrite B in *. rewrite (IH c H) in Hr1. discriminate Hr1.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne by apply B. apply (IH new_campaignID H).
              * destruct (FMap.find c (campaigns prev_state)) eqn:Hfind; auto.
        }
        (* B *)
        destruct (Z.of_nat (revealsNum c0) >? 0) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        * (* (revealsNum c0) > 0 *)    
          destruct (revealed p) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          unfold returnReward in receive_some. cbn in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
            ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some. 
          inversion receive_some. cbn.
          specialize IH as [L IH].
          rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
          rewrite total_returns_devide_new.
          set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
          unfold campaign_return in *; cbn in *.
          destruct (bountyPhase _ (bnum _)) eqn:B; try discriminate Hr3.
          destruct (Z.of_nat (revealsNum _) >? 0) eqn:B1; try discriminate Hr5.
          destruct (Z.of_nat (commitNum _) >? Z.of_nat (revealsNum _)) eqn:B2.
          -- (* RNG fail *)
            unfold refundsSum in *. cbn.
            rewrite (unrewardedNum_rewarded c0 (ctx_from ctx) p); cbn; auto; try lia.
            unfold calculateShare, fines. rewrite B2. lia.
          -- (* RNG success *)
            rewrite (unrewardedNum_rewarded c0 (ctx_from ctx) p); cbn; auto; try lia.
            unfold calculateShare. rewrite B2. lia.
        * (* (revealsNum c0) = 0 *)
          unfold returnReward in receive_some. cbn in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
            ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some.
          inversion receive_some. cbn. 
          specialize IH as [L IH].
          rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
          rewrite total_returns_devide_new.
          set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
          unfold campaign_return in *; cbn in *.
          destruct (bountyPhase _ (bnum _)) eqn:B; try discriminate Hr3. (* Hr3のため, chainはspecifyしない *)
          destruct (Z.of_nat (revealsNum _) >? 0) eqn:B1; try discriminate Hr5.
          unfold refundsSum in *; cbn in *.
          rewrite (unrewarded_participantsNum_rewarded c0 (ctx_from ctx) p); cbn; auto; try lia.
      + (* getRandom *)
        destruct (FMap.find c (campaigns prev_state)) eqn:H1; cbn in receive_some; try discriminate receive_some.
        inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* newCampaign *)
        destruct (timeLineCheck chain n n1 n2) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (moreThanZero n0) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_State_numCampaigns, set_State_numCampaigns in receive_some; cbn in receive_some.
        inversion receive_some. cbn. split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _].
            destruct (Nat.eqb ((FMap.size (campaigns prev_state) + 1)%nat) campaignID) eqn:B.
            + (* 新しく追加されたCampaign. IHは使えない  *)
              apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H. cbn in *. 
              unfold timeLineCheck, moreThanZero in *. cbn in *. 
              repeat split; try auto; try lia.
              * rewrite refundsSum_devide_new. cbn. rewrite FMap.remove_empty.
                unfold FMap.values. rewrite FMap.elements_empty. cbn. lia.
              * intros. rewrite FMap.find_empty in H2. discriminate H2. 
              * intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. rewrite FMap.find_empty in H2. discriminate H2.
              * intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. rewrite FMap.find_empty in H2. discriminate H2.              
              * intros. rewrite FMap.find_empty in H2. discriminate H2.
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              rewrite FMap.find_add_ne in H; auto. apply (IH campaignID campaign H).
          - (* campaignID is fresh *)
            intros. destruct IH as [_ IH].
            rewrite FMap.size_add_new in H; auto.
            rewrite FMap.find_add_ne; try lia. apply IH. lia.
        }
        (* B *)
        specialize IH as [[L1 L2] IH]. rewrite total_returns_devide_new. 
        rewrite fin_maps.delete_notin; auto; try lia. (* campaignID is fresh を使用 *)
        fold (total_returns {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state).
        unfold campaign_return in *; cbn in *.
        unfold bountyPhase, timeLineCheck in *. cbn.
        destruct (Z.of_nat (chain_height chain) <? Z.of_nat n) eqn:B; try lia.
      + (* returnBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (campaignFailed (commitNum c0) (revealsNum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (beConsumer ctx (consumer_addr c1)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers, 
          setter_from_getter_Consumer_bountypot, set_Consumer_bountypot in receive_some.
        inversion receive_some. cbn in *. 
        split.
        {
          (* A *)
          destruct IH as [IH _]. split; intros.
          - specialize IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H. cbn in *. 
              specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; auto; try lia.
              * rewrite refundsSum_devide_new.
                rewrite (refundsSum_devide_prev c0 (ctx_from ctx) c1) in L4; auto. cbn.
                specialize (L9 ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [L9 _].
                specialize (L9 c1) as [_ L9]; auto. lia.
              * specialize (L9 call_origin call_from call_amount) as [L9 _].
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. apply (L9 c1). auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * intros. specialize (L9 call_origin call_from call_amount) as [L9 _].
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. cbn. lia.   
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [_ L9].
                apply L9; auto. 
          + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
        - specialize IH as [_ IH]. rewrite FMap.size_add_existing in H. intros.
          destruct (Nat.eqb new_campaignID c) eqn:B.  
          * apply Nat.eqb_eq in B. rewrite B in *. rewrite (IH c H) in Hr1. discriminate Hr1.
          * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne by apply B. apply (IH new_campaignID H).
          * destruct (FMap.find c (campaigns prev_state)) eqn:Hfind; auto.
        }
        (* B *)
        specialize IH as [[L L1] IH].
        rewrite total_returns_devide_new.
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
          (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *.
        destruct (bountyPhase _ (bnum _)) eqn:B; try discriminate Hr2. (* Hr2のため, chainはspecifyしない *)
        unfold campaignFailed in Hr3. apply Bool.andb_false_iff in Hr3.
        destruct (Z.of_nat (revealsNum _) >? 0) eqn:B1; try lia. (* 矛盾？ *)
        * destruct (Z.of_nat (commitNum _) >? Z.of_nat (revealsNum _)) eqn:B2.
          -- (* RNG fail *)
            unfold unrewardedNum in *. simpl.
            rewrite refundsSum_devide_new.
            rewrite (refundsSum_devide_prev c0 (ctx_from ctx) c1 Hr4) in IH. cbn in *. lia. 
          -- (* RNG success. 矛盾 *)  
            rewrite Z.gtb_ltb in B2. apply Z.ltb_ge in B2.
            specialize (L c c0 Hr1) as [_ [_ [_ [_ [_ [_ [L _]]]]]]].
            assert (B3 : Z.of_nat c0.(revealsNum) <= Z.of_nat c0.(commitNum)).
            { rewrite L. lia. }
            destruct Hr3 as [B4|B4].
            ++ 
              specialize (Z.le_antisymm (Z.of_nat (commitNum c0)) (Z.of_nat (revealsNum c0)) B2 B3) as B5.
              apply Nat.eqb_neq in B4. apply Nat2Z.inj in B5. contradiction.
            ++ apply Bool.negb_false_iff in B4. apply Nat.eqb_eq in B4. lia.
        * (* revealsNum = 0 *)
          unfold unrewarded_participantsNum in *. simpl.
          rewrite refundsSum_devide_new.
          rewrite (refundsSum_devide_prev c0 (ctx_from ctx) c1 Hr4) in IH. cbn in *. lia. 
    - (* recursive *)
      assert (head_amount: act_body_amount head = ctx_amount ctx).
      {
        destruct head eqn:Hd.
        - simpl. apply action_facts.
        - simpl. apply action_facts.
        - auto.  
      }
      simpl in IH. rewrite head_amount in IH. unfold CallFacts in facts. 

      destruct msg as [msg|]; simpl in receive_some; try discriminate receive_some.
      destruct msg eqn:MSG; cbn in receive_some. 
      + (* numCampaigns *)
        inversion receive_some; cbn; rewrite H0 in *; split. apply IH. lia. 
      + (* campaigns *)
        destruct (result_of_option (FMap.find c (campaigns prev_state)) default_error); inversion receive_some.
        rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* founder *)
        inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* getCommitment *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some. 
        destruct (result_of_option (FMap.find (ctx_from ctx) (participants c0)) default_error) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* shaCommit *)
        unfold shaCommit_body in receive_some. inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* follow *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr2; cbn in receive_some.
        { 
          (* 二重 follow はエラー *)
          destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
          destruct (blankAddress (consumer_addr c1)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
          unfold blankAddress in Hr4.
          specialize IH as [[IH _] _]; auto.
          specialize (IH c c0 Hr1) as [_ [_ [_ [_ [_ [_ [_ [_ IH]]]]]]]]. 
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [IH _]. 
          specialize (IH c1 Hr2) as [IH _]. cbn in IH.
          rewrite IH in Hr4. rewrite null_address_not_valid in Hr4. discriminate Hr4.
        }
        destruct (checkFollowPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        unfold blankAddress in receive_some. rewrite address_eq_refl in receive_some. cbn in receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers in receive_some; cbn in receive_some.
        rewrite FMap.add_add in receive_some. inversion receive_some. cbn.    
        split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H; cbn in *. 
              specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; try apply IH; try lia; auto.
              * rewrite refundsSum_devide_new. unfold refundsSum in L4. cbn.
                rewrite <- fin_maps.delete_notin with (consumers c0) (ctx_from ctx) in L4; auto. lia.
              *  
                specialize (L9 call_origin call_from call_amount) as [L9 _].
                specialize (L9 consumer).
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _].
                specialize (L9 consumer).
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * apply (L9 call_origin call_from call_amount); auto. 
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
          - (* new_campaignID is fresh *)
            specialize IH as [_ IH]. 
            apply (new_campaignID_fresh_existing ctx prev_state c c0); auto.         
        }
        (* B *)
        specialize IH as [[L _] IH].
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
        rewrite total_returns_devide_new.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *. 
        destruct (bountyPhase {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} (bnum _)) eqn:B; try lia.
        specialize (L c c0 Hr1) as [L _].
        destruct (contraPhase_follow_bounty chain c0); auto.
      + (* commit *) 
        destruct (notBeBlank z) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkDeposit ctx (deposit c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkCommitPhase chain (bnum c0) (commitBalkline c0) (commitDeadline c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        {
          (* 二重 commit *)
          destruct (beBlank (commitment p)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          specialize IH as [[IH _] _].
          specialize (IH c c0 Hr2) as [_ [_ [_ [_ [_ [_ [_ [_ IH]]]]]]]].  
          specialize (IH ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [_ IH].
          unfold beBlank in Hr6. rewrite IH in Hr6; auto. discriminate Hr6.
        }
        destruct (FMap.find z (commitments c0)) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
        {
          (* commitments が存在 *)
          specialize IH as [[IH _] _].
          specialize (IH c c0 Hr2) as [_ [_ [_ [_ [_ [_ [_ [IH _]]]]]]]].
          specialize (IH z b). rewrite IH in receive_some; auto. cbn in receive_some; discriminate receive_some.
        }
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_commitments, set_Campaign_commitments,
          setter_from_getter_Campaign_commitNum, set_Campaign_commitNum, setter_from_getter_Campaign_participants, set_Campaign_participants in receive_some; cbn in receive_some.
        inversion receive_some; cbn. split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H; cbn in *. 
              specialize (IH c c0 Hr2) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; try apply IH; try lia; auto.
              * (* participant は追加されたが, revealed = false より変化無し *)
                unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_notin {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |}); auto.               
                simpl.
                rewrite filter_remove. apply Nat2Z.inj_le. rewrite notin_remove.
                -- unfold unrewardedNum in L5. lia.
                -- intro. apply filter_In in H2 as [contra _].
                  assert (A: ~ In (ctx_from ctx, {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |})
                  (FMap.elements (participants c0))).
                  apply FMap.not_In_elements; auto. contradiction.               
              * (* 参加者が追加されたため, unrewarded_participantsNum も増加 *)
                unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_notin); auto.  
                simpl. rewrite filter_remove. rewrite notin_remove.
                -- unfold unrewarded_participantsNum in L6. lia.
                -- intro. apply filter_In in H2 as [contra _].
                  assert (A: ~ In (ctx_from ctx, {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |})
                  (FMap.elements (participants c0))).
                  apply FMap.not_In_elements; auto. contradiction.
              * (* 以前はparticipant は存在しない *)
                rewrite replace_length_filter_add_notin; auto.
                simpl. rewrite filter_remove. rewrite notin_remove. lia.
                intro. apply filter_In in H2 as [contra _].
                assert (A: ~ In (ctx_from ctx, {| secret := 0; commitment := z; reward := 0; revealed := false; rewarded := false |})
                (FMap.elements (participants c0))).
                apply FMap.not_In_elements; auto. contradiction.
              * intros. destruct (Z.eqb hs z) eqn:B1.
                -- apply Z.eqb_eq in B1. rewrite B1 in *. rewrite FMap.find_add in H2. inversion H2. auto.
                -- apply Z.eqb_neq in B1. rewrite FMap.find_add_ne in H2; auto. 
                  apply (L8 hs); auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
              * intros. 
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. 
                  unfold notBeBlank in Hr1. auto.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto.
                  specialize (L9 call_origin call_from call_amount) as [_ L9].
                  apply (L9 participant); auto.
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              repeat (rewrite FMap.find_add_ne in H; auto). 
              apply (IH campaignID campaign H).
          - (* new_campaignID is fresh *)
            specialize IH as [_ IH]. intros.           
            rewrite FMap.size_add_existing in H; try (rewrite FMap.find_add; auto). 
            rewrite FMap.size_add_existing in H; try (rewrite FMap.find_add; auto).
            rewrite FMap.size_add_existing in H; auto. 
            + specialize (IH new_campaignID H). 
              destruct (Nat.eqb new_campaignID c) eqn:B. 
              * apply Nat.eqb_eq in B. rewrite B in IH. rewrite Hr2 in IH. discriminate IH. 
              * apply Nat.eqb_neq in B. repeat (rewrite FMap.find_add_ne; auto).
            + destruct (FMap.find c (campaigns _)) eqn:contra; auto.
        }
        (* B *)
        specialize IH as [[L _] IH]. repeat rewrite FMap.add_add.
        rewrite total_returns_devide_new. 
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr2) in IH.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *.
        destruct (bountyPhase {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} (bnum _)) eqn:B; try lia.
        * unfold checkDeposit in Hr3. apply Bool.negb_false_iff in Hr3. apply Z.eqb_eq in Hr3. 
          rewrite Hr3 in *. lia.
        * specialize (L c c0 Hr2) as [L _].
          destruct (contraPhase_commit_bounty chain c0); auto.
      + (* reveal *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (checkRevealPhase chain (bnum c0) (commitDeadline c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (checkSercret z (commitment p)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (revealed p) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants,
          setter_from_getter_Participant_revealed, set_Participant_revealed, setter_from_getter_Participant_secret, set_Participant_secret in receive_some; cbn in receive_some.
        inversion receive_some. cbn. split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H; cbn in *. 
              specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; try auto; try lia.
              * unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_existing p); auto.        
                simpl. destruct (rewarded _) eqn:B1; cbn.
                -- rewrite filter_remove. rewrite notin_remove.
                  ++ unfold unrewardedNum in L5. lia.
                  ++ intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto. (* rewarded は矛盾 *)
                -- rewrite filter_remove. rewrite notin_remove.
                  ++ unfold unrewardedNum in L5. lia.
                  ++ intro. apply filter_In in H2 as [_ contra]. rewrite Hr5 in contra. auto.
              * unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                rewrite (replace_length_filter_add_existing p); auto.  
                simpl. destruct (rewarded _) eqn:B1; cbn.
                -- rewrite filter_remove. rewrite notin_remove.
                  ++ unfold unrewarded_participantsNum in L6. lia.
                  ++ intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto. (* rewarded は矛盾 *)
                -- rewrite filter_remove. rewrite Nat2Z.inj_succ.
                  rewrite length_remove_NoDup.
                  ++ unfold unrewarded_participantsNum in L6. lia.
                  ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                  ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite B1. auto. 
              * rewrite (replace_length_filter_add_existing p); auto. 
                simpl. rewrite filter_remove. 
                rewrite length_remove_NoDup.
                -- lia. 
                -- apply List.NoDup_filter. apply FMap.NoDup_elements.
                -- apply FMap.In_elements in Hr2.
                  apply filter_In. split; auto. rewrite Hr5. auto. 
              * apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [L9 _].
                apply L9; auto.
              * intros. specialize (L9 call_origin call_from call_amount) as [_ L9].
                destruct (address_eqb call_from (ctx_from ctx)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. simpl. 
                  destruct (rewarded _) eqn:B2; try discriminate. intros.
                  apply (L9 p Hr2). auto. 
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto.
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
          - (* new_campaignID is fresh *)
            specialize IH as [_ IH]. 
            apply (new_campaignID_fresh_existing ctx prev_state c c0); auto.  
        }
          (* B *)
        specialize IH as [_ IH]. rewrite total_returns_devide_new. 
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *.
        destruct (bountyPhase {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} (bnum _)) eqn:B; try lia.
        destruct (contraPhase_reveal_bounty chain c0); auto.        
      + (* getMyBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (participants c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (rewarded p) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        split.
        {
          (* A *)
          destruct IH as [IH _].
          destruct (Z.of_nat (revealsNum c0) >? 0) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
          - destruct (revealed p) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
            unfold returnReward in receive_some. cbn in receive_some.
            unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
              ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some. 
            inversion receive_some. cbn. split; intros.
            + specialize IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
              * apply Nat.eqb_eq in B. rewrite B in *.
                rewrite FMap.find_add in H. inversion H. cbn in *. 
                specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
                repeat split; auto; try lia.
                -- unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                  rewrite (replace_length_filter_add_existing p); auto.            
                  simpl. rewrite Bool.andb_false_r.
                  rewrite filter_remove. rewrite length_remove_NoDup.
                  ++ unfold unrewardedNum in L5. lia.
                  ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                  ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite Hr4, Hr6. auto. 
                -- unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                  rewrite (replace_length_filter_add_existing p); auto.   
                  simpl. rewrite filter_remove. rewrite length_remove_NoDup.
                  ++ unfold unrewarded_participantsNum in L6. lia.
                  ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                  ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite Hr4. auto. 
                -- rewrite (replace_length_filter_add_existing p); auto. 
                  destruct (revealed _) eqn:B2; try discriminate Hr6; cbn.
                  rewrite filter_remove. rewrite notin_remove. lia.
                  intro. apply filter_In in H2 as [_ contra]. rewrite B2 in contra. auto.
                -- apply L9; auto.
                -- specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
                -- intros. specialize (L9 call_origin call_from call_amount) as [_ L9]. 
                  destruct (address_eqb call_from (ctx_from ctx)) eqn:B1.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                    rewrite <- B' in *. rewrite FMap.find_add in H2. inversion H2. simpl. intros.
                    apply (L9 p); auto.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                    rewrite FMap.find_add_ne in H2; auto.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
            + specialize IH as [_ IH]. rewrite FMap.size_add_existing in H. intros.
              destruct (Nat.eqb new_campaignID c) eqn:B.  
              * apply Nat.eqb_eq in B. rewrite B in *. rewrite (IH c H) in Hr1. discriminate Hr1.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne by apply B. apply (IH new_campaignID H).
              * destruct (FMap.find c (campaigns prev_state)) eqn:Hfind; auto.
          - (* (revealsNum c0) = 0 *)
            unfold returnReward in receive_some. cbn in receive_some.
            unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
              ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some. 
            inversion receive_some. cbn. split; intros.
            + specialize IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
              * apply Nat.eqb_eq in B. rewrite B in *.
                rewrite FMap.find_add in H. inversion H. cbn in *. 
                specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
                repeat split; auto; try lia.
                -- (* new_participant は入らない. *)
                  unfold unrewardedNum. cbn. apply Nat2Z.inj_le.
                  rewrite (replace_length_filter_add_existing p); auto.
                  unfold unrewardedNum. cbn.
                  simpl. rewrite Bool.andb_false_r. 
                  destruct (andb (revealed p) (negb (rewarded p))) eqn:B1; cbn.
                  ++ (* p が入ってる. 本当は矛盾 *)
                    rewrite filter_remove. rewrite length_remove_NoDup.
                    ** unfold unrewardedNum in L5. lia.
                    ** apply List.NoDup_filter. apply FMap.NoDup_elements.
                    ** apply filter_In. split; auto. apply FMap.In_elements; auto. 
                  ++ (* p が入っていない *)
                  rewrite filter_remove. rewrite notin_remove.
                    ** unfold unrewardedNum in L5. lia.
                    ** intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto. 
                -- (* unrewarded が減る *) 
                    unfold unrewarded_participantsNum. cbn. apply Nat2Z.inj_le.
                    rewrite (replace_length_filter_add_existing p); auto.  
                    simpl. rewrite filter_remove. rewrite length_remove_NoDup.
                    ++ unfold unrewarded_participantsNum in L6. lia.
                    ++ apply List.NoDup_filter. apply FMap.NoDup_elements.
                    ++ apply filter_In. split. apply FMap.In_elements; auto. rewrite Hr4. auto. 
                -- (* 変わらない. revealed p にかかわらず *) 
                  rewrite (replace_length_filter_add_existing p); auto.
                  destruct (revealed _) eqn:B1; cbn.
                  ++ rewrite filter_remove. rewrite notin_remove; auto. 
                    intro. apply filter_In in H2 as [_ contra]. rewrite B1 in contra. auto.
                  ++ rewrite filter_remove. rewrite Nat2Z.inj_succ. rewrite length_remove_NoDup.
                    ** lia. 
                    ** apply List.NoDup_filter. apply FMap.NoDup_elements.
                    ** apply filter_In. split. apply FMap.In_elements; auto. rewrite B1. auto. 
                -- apply L9; auto.
                -- specialize (L9 call_origin call_from call_amount) as [L9 _]. apply L9; auto.
                -- intros. specialize (L9 call_origin call_from call_amount) as [_ L9]. 
                  destruct (address_eqb call_from (ctx_from ctx)) eqn:B1.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                    rewrite <- B' in *. rewrite FMap.find_add in H2. inversion H2. simpl. intros.
                    apply (L9 p); auto.
                  ++ destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                    rewrite FMap.find_add_ne in H2; auto.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
            + specialize IH as [_ IH]. rewrite FMap.size_add_existing in H. intros.
              destruct (Nat.eqb new_campaignID c) eqn:B.  
              * apply Nat.eqb_eq in B. rewrite B in *. rewrite (IH c H) in Hr1. discriminate Hr1.
              * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
                rewrite FMap.find_add_ne by apply B. apply (IH new_campaignID H).
              * destruct (FMap.find c (campaigns prev_state)) eqn:Hfind; auto.
        }
        (* B *)
        destruct (Z.of_nat (revealsNum c0) >? 0) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        * (* (revealsNum c0) > 0 *)    
          destruct (revealed p) eqn:Hr6; cbn in receive_some; try discriminate receive_some.
          unfold returnReward in receive_some. cbn in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
            ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some. 
          inversion receive_some. cbn.
          specialize IH as [L IH].
          rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
          rewrite total_returns_devide_new.
          set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
          unfold campaign_return in *; cbn in *.
          destruct (bountyPhase _ (bnum _)) eqn:B; try discriminate Hr3.
          destruct (Z.of_nat (revealsNum _) >? 0) eqn:B1; try discriminate Hr5.
          destruct (Z.of_nat (commitNum _) >? Z.of_nat (revealsNum _)) eqn:B2.
          -- (* RNG fail *)
            unfold refundsSum in *. cbn.
            rewrite (unrewardedNum_rewarded c0 (ctx_from ctx) p); cbn; auto; try lia.
            unfold calculateShare, fines. rewrite B2. lia.
          -- (* RNG success *)
            rewrite (unrewardedNum_rewarded c0 (ctx_from ctx) p); cbn; auto; try lia.
            unfold calculateShare. rewrite B2. lia.
        * (* (revealsNum c0) = 0 *)
          unfold returnReward in receive_some. cbn in receive_some.
          unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_participants, set_Campaign_participants 
            ,setter_from_getter_Participant_rewarded, set_Participant_rewarded in receive_some; cbn in receive_some.
          inversion receive_some. cbn. 
          specialize IH as [L IH].
          rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
          rewrite total_returns_devide_new.
          set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
            (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
          unfold campaign_return in *; cbn in *.
          destruct (bountyPhase _ (bnum _)) eqn:B; try discriminate Hr3. (* Hr3のため, chainはspecifyしない *)
          destruct (Z.of_nat (revealsNum _) >? 0) eqn:B1; try discriminate Hr5.
          unfold refundsSum in *; cbn in *.
          rewrite (unrewarded_participantsNum_rewarded c0 (ctx_from ctx) p); cbn; auto; try lia.
      + (* getRandom *)
        destruct (FMap.find c (campaigns prev_state)) eqn:H1; cbn in receive_some; try discriminate receive_some.
        inversion receive_some; rewrite H0 in *; cbn; split. apply IH. lia. 
      + (* newCampaign *)
        destruct (timeLineCheck chain n n1 n2) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (moreThanZero n0) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_State_numCampaigns, set_State_numCampaigns in receive_some; cbn in receive_some.
        inversion receive_some. cbn. split.
        {
          (* A *)
          specialize IH as [IH _].
          split.
          - intros. destruct IH as [IH _].
            destruct (Nat.eqb ((FMap.size (campaigns prev_state) + 1)%nat) campaignID) eqn:B.
            + (* 新しく追加されたCampaign. IHは使えない  *)
              apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H. cbn in *. 
              unfold timeLineCheck, moreThanZero in *. cbn in *. 
              repeat split; try auto; try lia.
              * rewrite refundsSum_devide_new. cbn. rewrite FMap.remove_empty.
                unfold FMap.values. rewrite FMap.elements_empty. cbn. lia.
              * intros. rewrite FMap.find_empty in H2. discriminate H2. 
              * intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. rewrite FMap.find_empty in H2. discriminate H2.
              * intros. destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. rewrite FMap.find_empty in H2. discriminate H2.              
              * intros. rewrite FMap.find_empty in H2. discriminate H2.
            + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
              rewrite FMap.find_add_ne in H; auto. apply (IH campaignID campaign H).
          - (* campaignID is fresh *)
            intros. destruct IH as [_ IH].
            rewrite FMap.size_add_new in H; auto.
            rewrite FMap.find_add_ne; try lia. apply IH. lia.
        }
        (* B *)
        specialize IH as [[L1 L2] IH]. rewrite total_returns_devide_new. 
        rewrite fin_maps.delete_notin; auto; try lia. (* campaignID is fresh を使用 *)
        fold (total_returns {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state).
        unfold campaign_return in *; cbn in *.
        unfold bountyPhase, timeLineCheck in *. cbn.
        destruct (Z.of_nat (chain_height chain) <? Z.of_nat n) eqn:B; try lia.
      + (* returnBounty *)
        destruct (FMap.find c (campaigns prev_state)) eqn:Hr1; cbn in receive_some; try discriminate receive_some.
        destruct (bountyPhase chain (bnum c0)) eqn:Hr2; cbn in receive_some; try discriminate receive_some.
        destruct (campaignFailed (commitNum c0) (revealsNum c0)) eqn:Hr3; cbn in receive_some; try discriminate receive_some.
        destruct (FMap.find (ctx_from ctx) (consumers c0)) eqn:Hr4; cbn in receive_some; try discriminate receive_some.
        destruct (beConsumer ctx (consumer_addr c1)) eqn:Hr5; cbn in receive_some; try discriminate receive_some.
        unfold setter_from_getter_State_campaigns, set_State_campaigns, setter_from_getter_Campaign_consumers, set_Campaign_consumers, 
          setter_from_getter_Consumer_bountypot, set_Consumer_bountypot in receive_some.
        inversion receive_some. cbn in *. 
        split.
        {
          (* A *)
          destruct IH as [IH _]. split; intros.
          - specialize IH as [IH _]. destruct (Nat.eqb campaignID c) eqn:B.
            + apply Nat.eqb_eq in B. rewrite B in *.
              rewrite FMap.find_add in H. inversion H. cbn in *. 
              specialize (IH c c0 Hr1) as [L1 [L2 [L3 [L4 [L5 [L6 [L7 [L8 L9]]]]]]]].
              repeat split; auto; try lia.
              * rewrite refundsSum_devide_new.
                rewrite (refundsSum_devide_prev c0 (ctx_from ctx) c1) in L4; auto. cbn.
                specialize (L9 ctx.(ctx_origin) ctx.(ctx_from) ctx.(ctx_amount)) as [L9 _].
                specialize (L9 c1) as [_ L9]; auto. lia.
              * specialize (L9 call_origin call_from call_amount) as [L9 _].
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. apply (L9 c1). auto.  
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * intros. specialize (L9 call_origin call_from call_amount) as [L9 _].
                destruct (address_eqb call_from ctx.(ctx_from)) eqn:B1.
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [B'|]; try discriminate B1. 
                  rewrite B' in *. rewrite FMap.find_add in H2. inversion H2. cbn. lia.   
                -- destruct (address_eqb_spec call_from ctx.(ctx_from)) as [|B']; try discriminate B1.
                  rewrite FMap.find_add_ne in H2; auto. apply L9; auto.
              * specialize (L9 call_origin call_from call_amount) as [_ L9].
                apply L9; auto. 
          + rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne in H; try apply B. apply (IH campaignID campaign H).
        - specialize IH as [_ IH]. rewrite FMap.size_add_existing in H. intros.
          destruct (Nat.eqb new_campaignID c) eqn:B.  
          * apply Nat.eqb_eq in B. rewrite B in *. rewrite (IH c H) in Hr1. discriminate Hr1.
          * rewrite Nat.eqb_sym in B. apply Nat.eqb_neq in B. 
            rewrite FMap.find_add_ne by apply B. apply (IH new_campaignID H).
          * destruct (FMap.find c (campaigns prev_state)) eqn:Hfind; auto.
        }
        (* B *)
        specialize IH as [[L L1] IH].
        rewrite total_returns_devide_new.
        rewrite (total_returns_devide_prev {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |} prev_state c c0 Hr1) in IH.
        set (sumZ (campaign_return {| chain_height := chain_height chain; current_slot := current_slot chain; finalized_height := finalized_height chain |})
          (FMap.values (FMap.remove c (campaigns prev_state)))) as rest in *.
        unfold campaign_return in *; cbn in *.
        destruct (bountyPhase _ (bnum _)) eqn:B; try discriminate Hr2. (* Hr2のため, chainはspecifyしない *)
        unfold campaignFailed in Hr3. apply Bool.andb_false_iff in Hr3.
        destruct (Z.of_nat (revealsNum _) >? 0) eqn:B1; try lia. (* 矛盾？ *)
        * destruct (Z.of_nat (commitNum _) >? Z.of_nat (revealsNum _)) eqn:B2.
          -- (* RNG fail *)
            unfold unrewardedNum in *. simpl.
            rewrite refundsSum_devide_new.
            rewrite (refundsSum_devide_prev c0 (ctx_from ctx) c1 Hr4) in IH. cbn in *. lia. 
          -- (* RNG success. 矛盾 *)  
            rewrite Z.gtb_ltb in B2. apply Z.ltb_ge in B2.
            specialize (L c c0 Hr1) as [_ [_ [_ [_ [_ [_ [L _]]]]]]].
            assert (B3 : Z.of_nat c0.(revealsNum) <= Z.of_nat c0.(commitNum)).
            { rewrite L. lia. }
            destruct Hr3 as [B4|B4].
            ++ 
              specialize (Z.le_antisymm (Z.of_nat (commitNum c0)) (Z.of_nat (revealsNum c0)) B2 B3) as B5.
              apply Nat.eqb_neq in B4. apply Nat2Z.inj in B5. contradiction.
            ++ apply Bool.negb_false_iff in B4. apply Nat.eqb_eq in B4. lia.
        * (* revealsNum = 0 *)
          unfold unrewarded_participantsNum in *. simpl.
          rewrite refundsSum_devide_new.
          rewrite (refundsSum_devide_prev c0 (ctx_from ctx) c1 Hr4) in IH. cbn in *. lia. 
    - (* Permutaiton *)
      rewrite <- (sumZ_permutation perm). apply IH.
    - (* Facts *)
      unset_all. subst. 
      destruct_chain_step; auto. 
      + (* AddBlockFacts *)
        destruct valid_header as [valid_height _ _ _ _]. lia.
      + destruct_action_eval; auto.
        * (* DeployFacts *)
          rewrite Z.ge_le_iff in amount_nonnegative. auto.
        * (* CallFact *)
          rewrite Z.ge_le_iff in amount_nonnegative. auto. 
  Qed.

  Theorem enough_balance block_state randao_addr (trace : ChainTrace empty_state block_state) :
    env_contracts block_state randao_addr = Some (contract : WeakContract) ->
    exists (cstate : State),
      contract_state block_state randao_addr = Some cstate /\
      let chain := {| chain_height := block_state.(chain_height);
                      current_slot := block_state.(current_slot);
                      finalized_height := block_state.(finalized_height); |} in
      total_returns chain cstate <= (env_account_balances block_state randao_addr) - (sumZ act_body_amount (outgoing_acts block_state randao_addr)).
  Proof.
    intros.
    specialize (enough_balance_withlemma block_state randao_addr trace H). intro L.
    destruct L as [cstate L]. destruct L as [call_info L]. destruct L as [deploy_info L].
    specialize L as [L1 [L2 [L3 [_ L4]]]]. exists cstate. auto.
  Qed.

End Theories.