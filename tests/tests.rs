//! Tests for the `smart_contract_wallet` contract.
use concordium_cis2::*;
use concordium_smart_contract_testing::*;
use concordium_std::{PublicKeyEd25519, SchemaType, Serialize, SignatureEd25519, Serial, Deserial};
use gona_stake::*;
use primitive_types::*;


/// The tests accounts.
const ALICE: AccountAddress = AccountAddress([0; 32]);
const ALICE_ADDR: Address = Address::Account(ALICE);
const BOB: AccountAddress = AccountAddress([1; 32]);
const BOB_ADDR: Address = Address::Account(BOB);
const CHARLIE: AccountAddress = AccountAddress([2; 32]);
const CHARLIE_ADDR: Address = Address::Account(CHARLIE);

const ALICE_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([7; 32]);
const BOB_PUBLIC_KEY: PublicKeyEd25519 = PublicKeyEd25519([8; 32]);
const SERVICE_FEE_RECIPIENT_KEY: PublicKeyEd25519 = PublicKeyEd25519([9; 32]);

/// Initial balance of the accounts.
const ACC_INITIAL_BALANCE: Amount = Amount::from_ccd(10000);

const TOKEN_ID: TokenIdU8 = TokenIdU8(4);

const AIRDROP_TOKEN_AMOUNT: TokenAmountU64 = TokenAmountU64(9000000000000000000);

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
    token_id: TokenIdU8,
    data: AdditionalData
}

/// The withdraw message that is signed by the signer.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct WithdrawMessage<T: SigningAmount> {
    /// The entry_point that the signature is intended for.
    pub entry_point:           OwnedEntrypointName,
    /// A timestamp to make the signatures expire.
    pub expiry_time:           Timestamp,
    /// A nonce to prevent replay attacks.
    pub nonce:                 u64,
    /// The recipient public key of the service fee.
    pub service_fee_recipient: PublicKeyEd25519,
    /// The amount of CCD or tokens to be received as a service fee.
    pub service_fee_amount:    T,
    /// List of withdrawals.
    #[concordium(size_length = 2)]
    pub simple_withdraws:      Vec<Withdraw<T>>,
}
pub trait SigningAmount: Deserial + Serial {}

#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct Withdraw<T: SigningAmount> {
    /// The address receiving the CCD or tokens being withdrawn.
    pub to:              Receiver,
    /// The amount being withdrawn.
    pub withdraw_amount: T,
    /// Some additional data for the receive hook function.
    pub data:            AdditionalData,
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
    pub token_amount:                TokenAmountU256,
    /// The token id of the token signed in the message.
    pub token_id:                    ContractTokenId,
    /// The token contract of the token signed in the message.
    pub cis2_token_contract_address: ContractAddress,
}
trait IsMessage {
    fn expiry_time(&self) -> Timestamp;
    fn nonce(&self) -> u64;
}

impl<T: SigningAmount> IsMessage for WithdrawMessage<T> {
    fn expiry_time(&self) -> Timestamp { self.expiry_time }

    fn nonce(&self) -> u64 { self.nonce }
}
/// A batch of withdrawals signed by a signer.
#[derive(Serialize, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct WithdrawBatch<T: SigningAmount> {
    /// The signer public key.
    pub signer:    PublicKeyEd25519,
    /// The signature.
    pub signature: SignatureEd25519,
    /// The message being signed.
    pub message:   WithdrawMessage<T>,
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

    alice_deposits_cis2_tokens(
        &mut chain,
        smart_contract_wallet,
        cis2_token_contract_address,
        alice_public_key,
    );

    let service_fee_amount: TokenAmountU256 = TokenAmountU256(1.into());
    let withdraw_amount: TokenAmountU256 = TokenAmountU256(U256::from(900000000));
    let contract_token_id = TokenIdUnit();

    let message = WithdrawMessage {
        entry_point:           OwnedEntrypointName::new_unchecked("withdrawCis2Tokens".to_string()),
        expiry_time:           Timestamp::now(),
        nonce:                 0u64,
        service_fee_recipient: SERVICE_FEE_RECIPIENT_KEY,
        simple_withdraws:      vec![Withdraw {
            to:              Receiver::Contract(gona_stake_address, OwnedEntrypointName::new("chaperone_stake".to_owned()).unwrap()),
            withdraw_amount: TokenAmount {
                token_amount: withdraw_amount,
                token_id: contract_token_id,
                cis2_token_contract_address,
            },
            data:            AdditionalData::from(to_bytes(&alice_public_key)),
        }],
        service_fee_amount:    TokenAmount {
            token_amount: service_fee_amount,
            token_id: contract_token_id.clone(),
            cis2_token_contract_address,
        },
    };

    let mut withdraw = WithdrawBatch {
        signer:    alice_public_key,
        signature: DUMMY_SIGNATURE,
        message:   message.clone(),
    };

    // Get the message hash to be signed.
    let invoke = chain
        .contract_invoke(ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            address:      smart_contract_wallet,
            receive_name: OwnedReceiveName::new_unchecked(
                "smart_contract_wallet.getCis2WithdrawMessageHash".to_string(),
            ),
            message:      OwnedParameter::from_serial(&message)
                .expect("Should be a valid inut parameter"),
        })
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
                amount:       Amount::zero(),
                receive_name: OwnedReceiveName::new_unchecked(
                    "smart_contract_wallet.withdrawCis2Tokens".to_string(),
                ),
                address:      smart_contract_wallet,
                message:      OwnedParameter::from_serial(&withdraw_param)
                    .expect("Withdraw cis2 tokens params"),
            },
        )
        .expect("Should be able to withdraw cis2 tokens");



    
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

    // Load and deploy cis2 token module.
    let module =
        module_load_v1("tests/cis2_token/module.wasm.v1").expect("Module exists");
    let deployment =
        chain.module_deploy_v1_debug(SIGNER, ALICE, module, true).expect("Deploy valid module");

    // Initialize the token contract.
    let cis2_token_contract_init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_cis2_multi".to_string()),
            param:     OwnedParameter::from_serial(&AIRDROP_TOKEN_AMOUNT)
                .expect("Token amount params"),
        })
        .expect("Initialize contract");

    // Load and deploy the smart wallet module.
    let module = module_load_v1("tests/chaperone/module.wasm.v1").expect("Module exists");
    let deployment =
        chain.module_deploy_v1_debug(SIGNER, ALICE, module, true).expect("Deploy valid module");

    // Initialize the smart contract wallet.
    let smart_contract_wallet_init = chain
        .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
            amount:    Amount::zero(),
            mod_ref:   deployment.module_reference,
            init_name: OwnedContractName::new_unchecked("init_smart_contract_wallet".to_string()),
            param:     OwnedParameter::empty(),
        })
        .expect("Initialize contract");

     // Load and deploy the gona stake module.
     let module = module_load_v1("dist/stake.wasm.v1").expect("Module exists");
     let deployment =
         chain.module_deploy_v1_debug(SIGNER, ALICE, module, true).expect("Deploy valid module");
 
     // Initialize the smart contract wallet.
     let param = InitParam {
        admin: Address::Account(ALICE),
        decimals: 6,
        token_address: cis2_token_contract_init.contract_address,
        weight: 8500,
        smart_wallet: smart_contract_wallet_init.contract_address,
    };
    let param = OwnedParameter::from_serial(&param).unwrap();
     let gona_stake_init = chain
         .contract_init(SIGNER, ALICE, Energy::from(10000), InitContractPayload {
             amount:    Amount::zero(),
             mod_ref:   deployment.module_reference,
             init_name: OwnedContractName::new_unchecked("init_smart_contract_wallet".to_string()),
             param,
         })
         .expect("Initialize contract");

    (chain, smart_contract_wallet_init.contract_address, cis2_token_contract_init.contract_address, gona_stake_init.contract_address)
}




/// Alice deposits cis2 tokens into the smart contract wallet.
fn alice_deposits_cis2_tokens(
    chain: &mut Chain,
    smart_contract_wallet: ContractAddress,
    cis2_token_contract_address: ContractAddress,
    alice_public_key: PublicKeyEd25519,
) {
    let new_metadata_url = "https://new-url.com".to_string();

    let mint_param: MintParams = MintParams {
        to:           Receiver::Contract(
            smart_contract_wallet,
            OwnedEntrypointName::new_unchecked("depositCis2Tokens".to_string()),
        ),
        metadata_url: MetadataUrl {
            url:  new_metadata_url.clone(),
            hash: None,
        },
        token_id:     TOKEN_ID,
        data:         AdditionalData::from(to_bytes(&alice_public_key)),
    };

    // Deposit tokens.
    let _update = chain
        .contract_update(SIGNER, ALICE, ALICE_ADDR, Energy::from(10000), UpdateContractPayload {
            amount:       Amount::zero(),
            receive_name: OwnedReceiveName::new_unchecked("cis2_multi.mint".to_string()),
            address:      cis2_token_contract_address,
            message:      OwnedParameter::from_serial(&mint_param)
                .expect("Mint cis2 tokens params"),
        })
        .expect("Should be able to deposit cis2 tokens");

   
}

