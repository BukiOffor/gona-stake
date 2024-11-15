//! Tests for the `smart_contract_wallet` contract.
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::{Deserial, PublicKeyEd25519, SchemaType, Serial, Serialize, SignatureEd25519};
use gona_stake::*;
use primitive_types::*;

/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);
//const BOB_ADDR: Address = Address::Account(BOB);
const CHARLIE: AccountAddress = AccountAddress([2; 32]);
const CHARLIE_ADDR: Address = Address::Account(CHARLIE);

const ALICE_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([7; 32]);
const BOB_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([8; 32]);
const SERVICE_FEE_RECIPIENT_KEY: PublicKeyEd25519 = PublicKeyEd25519([9; 32]);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

const TOKEN_ID: TokenIdUnit = TokenIdUnit();
/// Airdrop amount = 100,000 * 1e6
const AIRDROP_TOKEN_AMOUNT: u64 = 100_000_000_000_000;
/// Pool token amount for rewards 500,000 * 1e6
const POOL_REWARD_AMOUNT: u64 = 500_000_000_000;
/// Amount to stake 50,000 * 1e6
const STAKE_AMOUNT: u64 = 50_000_000_000;
/// Half of the stake amount 25,000 * 1e6
const WITHDRAW_STAKE_AMOUNT: u64 = 25_000_000_000;
/// 100,000 * 1e6
const ALICE_KEY_AMOUNT: u64 = 100_000_000_000;
/// weight of rewards 8500 == 0.0085%
const WEIGHT:u32 = 8500;
/// Decimal of token: 6_u8
const DECIMALS: u8 = 6;
/// days of stake: 20_u64 days
const DAYS:u64 = 20;

const DUMMY_SIGNATURE: SignatureEd25519 = SignatureEd25519([
    68, 134, 96, 171, 184, 199, 1, 93, 76, 87, 144, 68, 55, 180, 93, 56, 107, 95, 127, 112, 24, 55,
    162, 131, 165, 91, 133, 104, 2, 5, 78, 224, 214, 21, 66, 0, 44, 108, 52, 4, 108, 10, 123, 75,
    21, 68, 42, 79, 106, 106, 87, 125, 122, 77, 154, 114, 208, 145, 171, 47, 108, 96, 221, 13,
]);

/// A signer for all the transactions.
const SIGNER: Signer = Signer::with_one_key();

#[derive(Serialize, SchemaType, Debug)]
pub struct MintParams {
    to: Receiver,
    metadata_url: MetadataUrl,
    token_id: TokenIdUnit,
    data: AdditionalData,
}

/// The withdraw message that is signed by the signer.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct WithdrawMessage<T: SigningAmount> {
    /// The entry_point that the signature is intended for.
    pub entry_point: OwnedEntrypointName,
    /// A timestamp to make the signatures expire.
    pub expiry_time: Timestamp,
    /// A nonce to prevent replay attacks.
    pub nonce: u64,
    /// The recipient public key of the service fee.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of CCD or tokens to be received as a service fee.
    pub service_fee_amount: T,
    /// List of withdrawals.
    #[concordium(size_length = 2)]
    pub simple_withdraws: Vec<Withdraw<T>>,
}
pub trait SigningAmount: Deserial + Serial {}

#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct Withdraw<T: SigningAmount> {
    /// The address receiving the CCD or tokens being withdrawn.
    pub to: Receiver,
    /// The amount being withdrawn.
    pub withdraw_amount: T,
    /// Some additional data for the receive hook function.
    pub data: AdditionalData,
}
/// `SigningAmount` trait definition for `Amount`.
impl SigningAmount for Amount {}
/// `SigningAmount` trait definition for `TokenAmount`.
impl SigningAmount for TokenAmount {}

/// The token amount signed in the message.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct TokenAmount {
    /// The token amount signed in the message.
    pub token_amount: TokenAmountU256,
    /// The token id of the token signed in the message.
    pub token_id: TokenIdUnit,
    /// The token contract of the token signed in the message.
    pub cis2_token_contract_address: ContractAddress,
}
pub trait IsMessage {
    fn expiry_time(&self) -> Timestamp;
    fn nonce(&self) -> u64;
}

impl<T: SigningAmount> IsMessage for WithdrawMessage<T> {
    fn expiry_time(&self) -> Timestamp {
        self.expiry_time
    }

    fn nonce(&self) -> u64 {
        self.nonce
    }
}
/// A batch of withdrawals signed by a signer.
#[derive(Serialize, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct WithdrawBatch<T: SigningAmount> {
    /// The signer public key.
    pub signer: PublicKeyEd25519,
    /// The signature.
    pub signature: SignatureEd25519,
    /// The message being signed.
    pub message: WithdrawMessage<T>,
}

/// The parameter type for the contract functions
/// `withdrawCcd/withdrawCis2Tokens`.
#[derive(Serialize, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
#[concordium(transparent)]
#[repr(transparent)]
pub struct WithdrawParameter<T: SigningAmount> {
    /// List of withdraw batches.
    #[concordium(size_length = 2)]
    pub withdraws: Vec<WithdrawBatch<T>>,
}

/// Test depositing of cis2 tokens.
#[test]
fn test_deposit_cis2_tokens() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address, gona_stake_address) =
        initialize_chain_and_contract();

    alice_deposits_cis2_tokens_and_fund_pool(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        ALICE_PUBLIC_KEY,
        gona_stake_address,
    );
}

/// Test signature of unstaking cis2 tokens.
#[test]
fn test_unstake_cis2_tokens_fails_if_signature_is_wrong() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address, gona_stake_address) =
        initialize_chain_and_contract();

    alice_deposits_cis2_tokens_and_fund_pool(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        ALICE_PUBLIC_KEY,
        gona_stake_address,
    );
}

#[test]
fn test_reward_amount_deposit() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address, gona_stake_address) =
        initialize_chain_and_contract();

    alice_deposits_cis2_tokens_and_fund_pool(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        ALICE_PUBLIC_KEY,
        gona_stake_address,
    );
    let res = view_reward_amount(&mut chain, gona_stake_address);
    assert_eq!(res, POOL_REWARD_AMOUNT, "pool reward does not equal amount")
}
#[test]
fn alice_set_paused() {
    let (mut chain, _, _, gona_stake) = initialize_chain_and_contract();
    // Deposit tokens.
    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("gona_stake.set_paused".to_string()),
                address: gona_stake,
                message: OwnedParameter::empty(),
            },
        )
        .expect("Should be able to pause a contract");
}

/// Test withdrawing of cis2 tokens.
#[test]
fn test_stake_cis2_tokens() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address, gona_stake_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_cis2_tokens_and_fund_pool(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
        gona_stake_address,
    );

    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
    println!(
        "{},{}.{}",
        balances.0[0].0, balances.0[1].0, balances.0[2].0
    );

    let service_fee_amount: TokenAmountU256 = TokenAmountU256(1.into());
    let withdraw_amount: TokenAmountU256 = TokenAmountU256(U256::from(90000000));

    let message = WithdrawMessage {
        entry_point: OwnedEntrypointName::new_unchecked("withdrawCis2Tokens".to_string()),
        expiry_time: Timestamp::now(),
        nonce: 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_withdraws: vec![Withdraw {
            to: Receiver::Contract(
                gona_stake_address,
                OwnedEntrypointName::new("chaperone_stake".to_owned()).unwrap(),
            ),
            withdraw_amount: TokenAmount {
                token_amount: withdraw_amount,
                token_id: TOKEN_ID,
                cis2_token_contract_address,
            },
            data: AdditionalData::from(to_bytes(&alice_public_key)),
        }],
        service_fee_amount: TokenAmount {
            token_amount: service_fee_amount,
            token_id: TOKEN_ID,
            cis2_token_contract_address,
        },
    };

    let mut withdraw = WithdrawBatch {
        signer: alice_public_key,
        signature: DUMMY_SIGNATURE,
        message: message.clone(),
    };
    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: smart_contract_wallet,
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.getCis2WithdrawMessageHash".to_string(),
                ),
                message: OwnedParameter::from_serial(&message)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query getCis2WithdrawMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    withdraw.signature = SignatureEd25519(signature.to_bytes());

    let withdraw_param = WithdrawParameter {
        withdraws: vec![withdraw],
    };

    let _update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.withdrawCis2Tokens".to_string(),
                ),
                address: smart_contract_wallet,
                message: OwnedParameter::from_serial(&withdraw_param)
                    .expect("Withdraw cis2 tokens params"),
            },
        )
        .expect("Should be able to withdraw cis2 tokens");
    let stake = get_stake_query(&mut chain, gona_stake_address, alice_public_key);
    println!("{:?}", stake);
    //assert_eq!(stake.is_some(), true, "Stake did not return")
}

/// This function simulates all the staking functionality. This includes the following tests:
    /// 1. Stake multiple times and reap reward for the time staked.
    /// 2. calculate the amount that was staked and earned determinstically. 
    /// 3. Verify balance of the cis5 smart wallet balance
    /// 4. verify balance of the token
#[test]
fn test_simulate_all_staking_functionality_for_chaperone_accounts() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address, gona_stake_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_cis2_tokens_and_fund_pool(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
        gona_stake_address,
    );

    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
   

    assert_eq!(
        balances.0[0].0, ALICE_KEY_AMOUNT,
        "Alice should have {}",
        ALICE_KEY_AMOUNT
    );
    let service_fee_amount: TokenAmountU256 = TokenAmountU256(0.into());
    let withdraw_amount: TokenAmountU256 = TokenAmountU256(U256::from(STAKE_AMOUNT));

    let message = WithdrawMessage {
        entry_point: OwnedEntrypointName::new_unchecked("withdrawCis2Tokens".to_string()),
        expiry_time: Timestamp::now(),
        nonce: 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_withdraws: vec![Withdraw {
            to: Receiver::Contract(
                gona_stake_address,
                OwnedEntrypointName::new("chaperone_stake".to_owned()).unwrap(),
            ),
            withdraw_amount: TokenAmount {
                token_amount: withdraw_amount,
                token_id: TOKEN_ID,
                cis2_token_contract_address,
            },
            data: AdditionalData::from(to_bytes(&alice_public_key)),
        }],
        service_fee_amount: TokenAmount {
            token_amount: service_fee_amount,
            token_id: TOKEN_ID,
            cis2_token_contract_address,
        },
    };

    let mut withdraw = WithdrawBatch {
        signer: alice_public_key,
        signature: DUMMY_SIGNATURE,
        message: message.clone(),
    };
    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: smart_contract_wallet,
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.getCis2WithdrawMessageHash".to_string(),
                ),
                message: OwnedParameter::from_serial(&message)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query getCis2WithdrawMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    withdraw.signature = SignatureEd25519(signature.to_bytes());

    let withdraw_param = WithdrawParameter {
        withdraws: vec![withdraw],
    };

    let _update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.withdrawCis2Tokens".to_string(),
                ),
                address: smart_contract_wallet,
                message: OwnedParameter::from_serial(&withdraw_param)
                    .expect("Withdraw cis2 tokens params"),
            },
        )
        .expect("Should be able to withdraw cis2 tokens");
    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
   
    assert_eq!(
        balances.0[0].0, STAKE_AMOUNT,
        "Balance is supposed to be 500,000,000,000 because we have staked 500,000,000"
    );
     // ff block time by 20 days and stake again
     chain.tick_block_time(Duration::from_days(DAYS)).unwrap();
    
     // calculate the reward time and amount
     // this algorithm should be determistic and rewards can always be calculated 
     // after a given amount of time in `DAYS`
     let reward = calculate_reward(&mut chain, gona_stake_address,alice_public_key);
     let reward_for_1st_stake = calculate_percent(STAKE_AMOUNT,WEIGHT, DECIMALS) * reward.days;
     println!("amount:{}, days: {}, reward:{}", reward.days, reward.rewards, reward.amount_staked);
     assert_eq!(reward.days, DAYS, "Days should equal 20");
     assert_eq!(reward_for_1st_stake, reward.rewards, "reward amount should be deterministic");




    // second stake; should increase the balance in the contract state
    // Since this is staking after 20 days, the stake should accumulate rewards for 20 days 
    // then reset the time of stake to 0.
    // then the new stake reward will be calculated the the new balance that is
    // prev_state_balance + previous_accumulated_result from the 1st stake
    let message = WithdrawMessage {
        entry_point: OwnedEntrypointName::new_unchecked("withdrawCis2Tokens".to_string()),
        expiry_time: Timestamp::now(),
        nonce: 1u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_withdraws: vec![Withdraw {
            to: Receiver::Contract(
                gona_stake_address,
                OwnedEntrypointName::new("chaperone_stake".to_owned()).unwrap(),
            ),
            withdraw_amount: TokenAmount {
                token_amount: withdraw_amount,
                token_id: TOKEN_ID,
                cis2_token_contract_address,
            },
            data: AdditionalData::from(to_bytes(&alice_public_key)),
        }],
        service_fee_amount: TokenAmount {
            token_amount: service_fee_amount,
            token_id: TOKEN_ID,
            cis2_token_contract_address,
        },
    };

    let mut withdraw = WithdrawBatch {
        signer: alice_public_key,
        signature: DUMMY_SIGNATURE,
        message: message.clone(),
    };
    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: smart_contract_wallet,
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.getCis2WithdrawMessageHash".to_string(),
                ),
                message: OwnedParameter::from_serial(&message)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query getCis2WithdrawMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    withdraw.signature = SignatureEd25519(signature.to_bytes());

    let withdraw_param = WithdrawParameter {
        withdraws: vec![withdraw],
    };

    let _update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.withdrawCis2Tokens".to_string(),
                ),
                address: smart_contract_wallet,
                message: OwnedParameter::from_serial(&withdraw_param)
                    .expect("Withdraw cis2 tokens params"),
            },
        )
        .expect("Should be able to withdraw cis2 tokens");

    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );

    // you have staked the total balance that you have into the gona_stake
    // so the new balance should be `0`
    assert_eq!(balances.0[0].0, 0, "Balance is supposed to be Zero");

    // check if stake exists in the state and calcuate the determinstic amount
    // this amount should be the previous stake amount`STAKE_AMOUNT` + `reward_for_1st_stake`
    let stake = get_stake_query(&mut chain, gona_stake_address, alice_public_key)
        .expect("This stake should exist in state, Damn");
    
    // this is the stake amount + rewards earned in 20 days
    let second_stake_balance = STAKE_AMOUNT + reward_for_1st_stake;
    assert_eq!(stake.amount.0, second_stake_balance,
     "SecondStake::New state balance should add to the reward of the first stake");

    // calculate the new time and assert that the time of stake has been reset 
    let now = chain.block_time();
    let new_time = stake.time_of_stake.duration_between(now).days() ;
    assert_eq!(new_time, 0, "SecondStake:: We reset the time of first stake to 0 becaome rewards have been earned for that duration" );
    
    // ff block time by 20 days
    // this will fast forward the days of active stake to 40 days
    // but the contract state will read an active stake days of 20
    // because you have earned a reward for the first 20 days.
    chain.tick_block_time(Duration::from_days(20)).unwrap();
    
    // calculate the reward time and amount
    // reward time should be `DAYS`<20> because the contract reseted the time of stake after the second stake
    // reward amount will be calculated with new the predetermined balance from the second stake
    
    let reward = calculate_reward(&mut chain, gona_stake_address,alice_public_key);

    let calculated_reward = calculate_percent(second_stake_balance,WEIGHT,DECIMALS) * reward.days ;
    println!("reward: {} days {} amount", reward.days, reward.rewards);
    assert_eq!(reward.days, DAYS, "Days should equal 20 because time has been reset");
    assert_eq!(calculated_reward, reward.rewards, "Rewards should be calculated determinstically");
    assert_eq!(second_stake_balance, reward.amount_staked, "Balance should be equal second balance");
}


/// calculates the actual reward in the `test_stake_cis2_token_twice_and_increase_balance()`
#[test]
fn calculate_rewards() {
    let (
        mut chain, smart_contract_wallet, 
        cis2_token_contract_address, 
        gona_stake_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::SigningKey;

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_cis2_tokens_and_fund_pool(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
        gona_stake_address,
    );
   

}
fn calculate_reward( 
    chain: &mut Chain,     
    gona_stake: ContractAddress,
    alice_public_key: PublicKeyEd25519,
    ) -> RewardResult {
        let staker: Staker = Staker::Chaperone(alice_public_key);
        let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "gona_stake.calculate_rewards".to_string(),
                ),
                address: gona_stake,
                message: OwnedParameter::from_serial(&staker).expect("Staker could not be serialized"),
            },
        )
        .expect("Invoke Stake Query");
    let res: RewardResult = invoke
        .parse_return_value()
        .expect("Damn, the hell happened");
    res
}

#[test]
fn test_unstake_cis2_tokens_of_chaperone() {
    let (mut chain, smart_contract_wallet, cis2_token_contract_address, gona_stake_address) =
        initialize_chain_and_contract();

    use ed25519_dalek::{Signer, SigningKey};

    let rng = &mut rand::thread_rng();

    // Construct signing key.
    let signing_key = SigningKey::generate(rng);
    let alice_public_key = PublicKeyEd25519(signing_key.verifying_key().to_bytes());

    alice_deposits_cis2_tokens_and_fund_pool(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
        gona_stake_address,
    );

    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );
   
    assert_eq!(
        balances.0[0].0, ALICE_KEY_AMOUNT,
        "Alice should have {}",
        ALICE_KEY_AMOUNT
    );

    let service_fee_amount: TokenAmountU256 = TokenAmountU256(0.into());
    let withdraw_amount: TokenAmountU256 = TokenAmountU256(U256::from(STAKE_AMOUNT));

    let message = WithdrawMessage {
        entry_point: OwnedEntrypointName::new_unchecked("withdrawCis2Tokens".to_string()),
        expiry_time: Timestamp::now(),
        nonce: 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_withdraws: vec![Withdraw {
            to: Receiver::Contract(
                gona_stake_address,
                OwnedEntrypointName::new("chaperone_stake".to_owned()).unwrap(),
            ),
            withdraw_amount: TokenAmount {
                token_amount: withdraw_amount,
                token_id: TOKEN_ID,
                cis2_token_contract_address,
            },
            data: AdditionalData::from(to_bytes(&alice_public_key)),
        }],
        service_fee_amount: TokenAmount {
            token_amount: service_fee_amount,
            token_id: TOKEN_ID,
            cis2_token_contract_address,
        },
    };

    let mut withdraw = WithdrawBatch {
        signer: alice_public_key,
        signature: DUMMY_SIGNATURE,
        message: message.clone(),
    };
    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: smart_contract_wallet,
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.getCis2WithdrawMessageHash".to_string(),
                ),
                message: OwnedParameter::from_serial(&message)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query getCis2WithdrawMessageHash");

    let signature = signing_key.sign(&invoke.return_value);

    withdraw.signature = SignatureEd25519(signature.to_bytes());

    let withdraw_param = WithdrawParameter {
        withdraws: vec![withdraw],
    };

    // send tokens from smart wallet to stake contract
    // this is the act of staking
    let _update = chain
        .contract_update(
            SIGNER,
            CHARLIE,
            CHARLIE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.withdrawCis2Tokens".to_string(),
                ),
                address: smart_contract_wallet,
                message: OwnedParameter::from_serial(&withdraw_param)
                    .expect("Withdraw cis2 tokens params"),
            },
        )
        .expect("Should be able to withdraw cis2 tokens");

    // assert if the stake was successful
    let stake = get_stake_query(&mut chain, gona_stake_address, alice_public_key);
    assert_eq!(stake.is_some(), true, "Stake did not return");

    // assert stake amount should match amount that was staked
    assert_eq!(stake.unwrap().amount.0, STAKE_AMOUNT, "Stake State Balance should match the balance");

    let balances = get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
        &chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );

    // Balance should be equal to the stake amount since we are staking half of the assets
    assert!(
        balances.0[0].0 == STAKE_AMOUNT,
        "Balance should be equal to the stake amount since we are staking half of the assets"
    );
    chain
        .tick_block_time(Duration::from_days(DAYS))
        .expect("days should be ticked");

    // calculate the reward time and amount
     // this algorithm should be determistic and rewards can always be calculated 
     // after a given amount of time in `DAYS`
     let reward = calculate_reward(&mut chain, gona_stake_address,alice_public_key);
     let reward_for_1st_stake = calculate_percent(STAKE_AMOUNT,WEIGHT, DECIMALS) * reward.days;
     println!("amount:{}, days: {}, reward:{}", reward.days, reward.rewards, reward.amount_staked);
     assert_eq!(reward.days, DAYS, "Days should equal 20");
     assert_eq!(reward_for_1st_stake, reward.rewards, "reward amount should be deterministic");

    release_stake(
        &mut chain,
        gona_stake_address,
        alice_public_key,
        signing_key,
        WITHDRAW_STAKE_AMOUNT - 10_000_000_000,
    );



    let reward_after_release = calculate_reward(&mut chain, gona_stake_address,alice_public_key);
    println!("{}", reward_after_release.amount_staked);


    let stake = get_stake_query(&mut chain, gona_stake_address, alice_public_key)
        .expect("stake should exist");
    println!("the stake: {:?}", stake);

    let res = view_reward_amount(&mut chain, gona_stake_address);
    assert_ne!(res,POOL_REWARD_AMOUNT,"pool reward should be depleted since an amount was paid out")
}

pub type Sha256 = [u8; 32];
#[derive(Serialize, SchemaType, Clone, PartialEq, Eq, Debug)]
pub struct SetMetadataUrlParams {
    /// The URL following the specification RFC1738.
    pub url: String,
    /// The hash of the document stored at the above URL.
    pub hash: Option<Sha256>,
}

// Helpers:

/// Setup chain and contract.
///
/// Also creates the three accounts, Alice, Bob, and Charlie.
///
/// Alice is the owner of the contract.
fn initialize_chain_and_contract() -> (Chain, ContractAddress, ContractAddress, ContractAddress) {
    let mut chain = Chain::new();

    // Create some accounts on the chain.
    chain.create_account(Account::new(ALICE, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(BOB, ACC_INITIAL_BALANCE));
    chain.create_account(Account::new(CHARLIE, ACC_INITIAL_BALANCE));

    let metadata = SetMetadataUrlParams {
        url: "https://www.example.come".to_string(),
        hash: None,
    };
    // Load and deploy cis2 token module.
    let module = module_load_v1("tests/cis2_token/module.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1_debug(SIGNER, ALICE, module, true)
        .expect("Deploy valid module");

    // Initialize the token contract.
    let cis2_token_contract_init = chain
        .contract_init(
            SIGNER,
            ALICE,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_gona_token".to_string()),
                param: OwnedParameter::from_serial(&metadata).expect("Token amount params"),
            },
        )
        .expect("Initialize contract");

    // Load and deploy the smart wallet module.
    let module = module_load_v1("tests/chaperone/module.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1_debug(SIGNER, ALICE, module, true)
        .expect("Deploy valid module");

    // Initialize the smart contract wallet.
    let smart_contract_wallet_init = chain
        .contract_init(
            SIGNER,
            ALICE,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: deployment.module_reference,
                init_name: OwnedContractName::new_unchecked(
                    "init_smart_contract_wallet".to_string(),
                ),
                param: OwnedParameter::empty(),
            },
        )
        .expect("Initialize contract");

    // Load and deploy the gona stake module.
    let module = module_load_v1("dist/stake.wasm.v1").expect("Module exists");
    let deployment = chain
        .module_deploy_v1_debug(SIGNER, ALICE, module, true)
        .expect("Deploy valid module");

    // Initialize the smart contract wallet.
    let param = InitParam {
        admin: Address::Account(ALICE),
        decimals: DECIMALS,
        token_address: cis2_token_contract_init.contract_address,
        weight: WEIGHT,
        smart_wallet: smart_contract_wallet_init.contract_address,
    };
    let param = OwnedParameter::from_serial(&param).unwrap();
    let gona_stake_init = chain
        .contract_init(
            SIGNER,
            ALICE,
            Energy::from(10000),
            InitContractPayload {
                amount: Amount::zero(),
                mod_ref: deployment.module_reference,
                init_name: OwnedContractName::new_unchecked("init_gona_stake".to_string()),
                param,
            },
        )
        .expect("Initialize contract");

    (
        chain,
        smart_contract_wallet_init.contract_address,
        cis2_token_contract_init.contract_address,
        gona_stake_init.contract_address,
    )
}

#[derive(SchemaType, Serialize, PartialEq, Eq, Debug)]
pub struct MintParam {
    token_id: TokenIdUnit,
    amount: TokenAmountU64,
    owner: Address,
}

/// Alice deposits cis2 tokens into the smart contract wallet.
fn alice_deposits_cis2_tokens_and_fund_pool(
    chain: &mut Chain,
    smart_contract_wallet: ContractAddress,
    cis2_token_contract_address: ContractAddress,
    alice_public_key: PublicKeyEd25519,
    gona_stake_address: ContractAddress,
) {
    let mint_param: MintParam = MintParam {
        owner: Address::Account(ALICE),
        token_id: TOKEN_ID,
        amount: TokenAmountU64(AIRDROP_TOKEN_AMOUNT),
    };

    //Deposit tokens.
    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("gona_token.mint".to_string()),
                address: cis2_token_contract_address,
                message: OwnedParameter::from_serial(&mint_param).expect("Mint cis2 tokens params"),
            },
        )
        .expect("Should be able to deposit cis2 tokens");

    // // Create a Transfer instance
    let transfer_payload = concordium_cis2::Transfer {
        token_id: TOKEN_ID,
        amount: TokenAmountU64(ALICE_KEY_AMOUNT),
        to: Receiver::Contract(
            smart_contract_wallet,
            OwnedEntrypointName::new_unchecked("depositCis2Tokens".into()),
        ),
        from: ALICE_ADDR,
        data: AdditionalData::from(to_bytes(&alice_public_key)),
    };
    // Create a Transfer instance
    let transfer_pool_payload = concordium_cis2::Transfer {
        token_id: TOKEN_ID,
        amount: TokenAmountU64(POOL_REWARD_AMOUNT),
        to: Receiver::Contract(
            gona_stake_address,
            OwnedEntrypointName::new_unchecked("depositCis2Tokens".into()),
        ),
        from: ALICE_ADDR,
        data: AdditionalData::empty(),
    };
    let mut transfers = Vec::new();
    transfers.push(transfer_payload);
    transfers.push(transfer_pool_payload);

    let payload = TransferParams::from(transfers);
    // Deposit tokens.
    let _update = chain
        .contract_update(
            SIGNER,
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked("gona_token.transfer".to_string()),
                address: cis2_token_contract_address,
                message: OwnedParameter::from_serial(&payload).expect("Mint cis2 tokens params"),
            },
        )
        .expect("Should be able to deposit cis2 tokens");
}

pub type ContractBalanceOfQueryParams = BalanceOfQueryParams<TokenIdUnit>;

pub type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;
/// The parameter type for the contract function `ccdBalanceOf`.
#[derive(Serialize, SchemaType, PartialEq, Eq)]
#[concordium(transparent)]
#[repr(transparent)]
pub struct Cis2BalanceOfResponse(#[concordium(size_length = 2)] pub Vec<ContractTokenAmount>);

/// Conversion helper function.
impl From<Vec<ContractTokenAmount>> for Cis2BalanceOfResponse {
    fn from(results: Vec<ContractTokenAmount>) -> Self {
        Cis2BalanceOfResponse(results)
    }
}

#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
#[repr(transparent)]
pub struct Cis2BalanceOfParameter {
    /// List of balance queries.
    #[concordium(size_length = 2)]
    pub queries: Vec<Cis2BalanceOfQuery>,
}
/// A query for the token balance of a given public key.
#[derive(Serialize, SchemaType)]
pub struct Cis2BalanceOfQuery {
    /// The ID of the token.
    pub token_id: TokenIdUnit,
    /// The token contract address.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key.
    pub public_key: PublicKeyEd25519,
}

/// The parameter type for the contract function `cis2BalanceOf`.
#[derive(Serialize, SchemaType)]
#[concordium(transparent)]
#[repr(transparent)]
pub struct Cis2BalanceOfAccount {
    /// List of balance queries.
    pub queries: Cis2BalanceOfQuery,
}

fn get_cis2_token_balances_from_alice_and_bob_and_service_fee_recipient(
    chain: &Chain,
    smart_contract_wallet: ContractAddress,
    cis2_token_contract_address: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) -> Cis2BalanceOfResponse {
    let balance_of_params = Cis2BalanceOfParameter {
        queries: vec![
            Cis2BalanceOfQuery {
                token_id: TOKEN_ID,
                cis2_token_contract_address,
                public_key: alice_public_key,
            },
            Cis2BalanceOfQuery {
                token_id: TOKEN_ID,
                cis2_token_contract_address,
                public_key: BOB_PUBLIC_KEY,
            },
            Cis2BalanceOfQuery {
                token_id: TOKEN_ID,
                cis2_token_contract_address,
                public_key: SERVICE_FEE_RECIPIENT_KEY,
            },
        ],
    };
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.cis2BalanceOf".to_string(),
                ),
                address: smart_contract_wallet,
                message: OwnedParameter::from_serial(&balance_of_params)
                    .expect("CIS-2 BalanceOf params"),
            },
        )
        .expect("Invoke CIS-2 BalanceOf");
    let rv: Cis2BalanceOfResponse = invoke
        .parse_return_value()
        .expect("CIS-2 BalanceOf return value");
    rv
}

fn get_stake_query(
    chain: &mut Chain,
    gona_stake: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) -> StakeQuery {
    let staker = Staker::Chaperone(alice_public_key);
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "gona_stake.get_stake_info".to_string(),
                ),
                address: gona_stake,
                message: OwnedParameter::from_serial(&staker).expect("Damn, wth happened"),
            },
        )
        .expect("Invoke Stake Query");
    let sq: StakeQuery = invoke
        .parse_return_value()
        .expect("Damn, the hell happened");
    sq
}

fn view_reward_amount(chain: &mut Chain, gona_stake: ContractAddress) -> u64 {
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "gona_stake.view_reward_volume".to_string(),
                ),
                address: gona_stake,
                message: OwnedParameter::empty(),
            },
        )
        .expect("Invoke Stake Query");
    let res: u64 = invoke
        .parse_return_value()
        .expect("Damn, the hell happened");
    res
}
fn release_stake(
    chain: &mut Chain,
    gona_stake: ContractAddress,
    alice_public_key: PublicKeyEd25519,
    signing_key: ed25519_dalek::SigningKey,
    amount: u64,
) {
    use ed25519_dalek::Signer;

    let staker = Staker::Chaperone(alice_public_key);
    let message = WithdrawStakeForChaperone {
        amount: TokenAmountU64(amount),
        token_id: TOKEN_ID,
        owner: staker.clone(),
        expiry_time: Timestamp::from_timestamp_millis(70000000000),
        entry_point: "depositCis2Tokens".to_string(),
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                address: gona_stake,
                receive_name: OwnedReceiveName::new_unchecked(
                    "gona_stake.get_param_hash".to_string(),
                ),
                message: OwnedParameter::from_serial(&message)
                    .expect("Should be a valid inut parameter"),
            },
        )
        .expect("Should be able to query the message hash");

    let signature = signing_key.sign(&invoke.return_value);

    let signature = SignatureEd25519(signature.to_bytes());
    let payload = Payload {
        signer: alice_public_key,
        message,
        signature,
    };
    let param = WithdrawStake {
        amount: TokenAmountU64(amount),
        token_id: TOKEN_ID,
        owner: staker.clone(),
        additional_data: Some(payload),
    };

    // {
    //     use std::thread;
    //     use std::time::Duration;

    //     thread::sleep(Duration::from_secs(1));
    //     println!("Resumed after 1 seconds.");
    // }

    let _invoke = chain
        .contract_invoke(
            ALICE,
            ALICE_ADDR,
            Energy::from(10000),
            UpdateContractPayload {
                amount: Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "gona_stake.withdraw_stake".to_string(),
                ),
                address: gona_stake,
                message: OwnedParameter::from_serial(&param).expect("Damn, wth happened"),
            },
        )
        .expect("Invoke Stake Query");
}

fn calculate_percent(amount: u64, weight: u32, decimals: u8) -> u64 {
    (amount * (weight as u64)) / (100 * (10_i32.pow(decimals as u32) as u64))
}