#![cfg_attr(not(feature = "std"), no_std)]

use concordium_cis2::*;
use concordium_std::Amount;
use concordium_std::*;
use core::fmt::Debug;
use types::IsMessage;
pub mod types;
use types::*;

#[cfg(feature = "serde")]
use serde::{Deserialize as SerdeDeserialize, Serialize as SerdeSerialize};

/// smallest possible token ID.
pub type ContractTokenId = TokenIdUnit;
pub type ContractTokenAmount = TokenAmountU64;

// The testnet genesis hash is:
// 0x4221332d34e1694168c2a0c0b3fd0f273809612cb13d000d5c2e00e85f50f796
const TESTNET_GENESIS_HASH: [u8; 32] = [
    66, 33, 51, 45, 52, 225, 105, 65, 104, 194, 160, 192, 179, 253, 15, 39, 56, 9, 97, 44, 177, 61,
    0, 13, 92, 46, 0, 232, 95, 80, 247, 150,
];
pub const TOKEN_ID_GONA: ContractTokenId = TokenIdUnit();
type Cis2TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

#[derive(Serialize, SchemaType, Clone, Debug)]
pub struct Chaperone {
    pub contract_address: ContractAddress,
    pub key: PublicKeyEd25519,
}

#[derive(Serialize, SchemaType, Clone, Debug)]
pub enum Staker {
    Account(AccountAddress),
    Chaperone(PublicKeyEd25519),
}

/// Struct to represent information about a stake.
#[derive(Serialize, SchemaType, PartialEq, Eq, Clone, Debug)]
pub struct StakeEntry {
    pub amount: TokenAmountU64,
    pub time_of_stake: Timestamp,
    pub token_id: TokenIdUnit,
}

#[derive(Serialize, Clone, Debug, SchemaType)]
pub struct WithdrawStake {
    pub amount: TokenAmountU64,
    pub owner: Staker,
    pub token_id: TokenIdUnit,
    pub additional_data: Option<Payload>,
}

#[derive(Serialize, Clone, Debug, SchemaType)]
pub struct WithdrawStakeOfAccount {
    pub amount: TokenAmountU64,
    pub owner: Staker,
    pub token_id: TokenIdUnit,
}

#[derive(Serialize, Clone, Debug, SchemaType)]
pub struct Payload {
    /// The signer public key.
    pub signer: PublicKeyEd25519,
    /// The signature.
    pub signature: SignatureEd25519,
    /// The message that was signed.
    pub message: WithdrawStakeForChaperone,
}

#[derive(Serialize, Clone, Debug, SchemaType)]
pub struct WithdrawStakeForChaperone {
    pub amount: TokenAmountU64,
    pub owner: Staker,
    pub token_id: TokenIdUnit,
    pub expiry_time: Timestamp,
    pub entry_point: String,
}

impl IsMessage for WithdrawStakeForChaperone {
    fn expiry_time(&self) -> Timestamp {
        self.expiry_time
    }
}

/// Error types
#[derive(Debug, PartialEq, Eq, Clone, Reject, Serialize, SchemaType)]
pub enum StakingError {
    StakingNotFound,
    InsufficientFunds,
    InvalidPrice,
    InvalidReleaseTime,
    InvalidStakingState,
    #[from(ParseError)]
    ParseParams,
    #[from(TransferError)]
    TransferError,
    ContractInvokeError,
    OnlyContractCanStake,
    SenderContractAddressIsNotAllowedToStake,
    CannotStakeLessThanAllowAmount,
    SenderIsNotOwner,
    DaysOfStakeCouldNotBeCalculated,
    SenderIsNotAdmin,
    Expired,
    WrongSignature,
    SignatureVerficationFailed,
    CouldNotParseAdditionalData,
    Overflow
}

impl<A> From<CallContractError<A>> for StakingError {
    fn from(_: CallContractError<A>) -> Self {
        Self::ContractInvokeError
    }
}

#[derive(Serialize, SchemaType)]
pub struct StakeParams {
    pub staker: Staker,
    pub amount: ContractTokenAmount,
}

/// A single withdrawal of CCD or some amount of tokens.
#[derive(Serialize, Clone, SchemaType)]
#[cfg_attr(feature = "serde", derive(SerdeSerialize, SerdeDeserialize))]
pub struct Withdraw {
    /// The address receiving the CCD or tokens being withdrawn.
    pub to: Receiver,
    /// The amount being withdrawn.
    pub withdraw_amount: ContractTokenAmount,
    /// Some additional data for the receive hook function.
    pub data: AdditionalData,
    pub token_id: ContractTokenId,
}

#[derive(Serialize, SchemaType)]
pub struct ReleaseFundsParams {
    pub token_id: ContractTokenId,
}

#[derive(Serialize, SchemaType)]
struct UpgradeParams {
    /// The new module reference.
    module: ModuleReference,
    /// Optional entrypoint to call in the new module after upgrade.
    migrate: Option<(OwnedEntrypointName, OwnedParameter)>,
}

#[derive(Serialize, SchemaType)]
pub struct InitParam {
    /// The contract address of the token.
    pub token_address: ContractAddress,
    /// The weight at which rewards are calculated, should be in percentage
    pub weight: u32,
    /// the decimals of the token contract,
    pub decimals: u8,
    pub admin: Address,
    pub smart_wallet: ContractAddress,
}

/// Smart contract state
#[derive(Serial, DeserialWithState)]
#[concordium(state_parameter = "S")]
pub struct State<S = StateApi> {
    pub stake_entries: StateMap<Staker, StakeEntry, S>,
    pub decimals: u8,
    pub token_address: ContractAddress,
    pub weight: u32,
    pub paused: bool,
    pub admin: Address,
    pub smart_wallet: ContractAddress,
    pub reward_volume: u64

}

impl State {
    fn empty(
        state_builder: &mut StateBuilder,
        token_address: ContractAddress,
        weight: u32,
        decimals: u8,
        admin: Address,
        smart_wallet: ContractAddress,
    ) -> Self {
        State {
            stake_entries: state_builder.new_map(),
            decimals,
            token_address,
            weight,
            paused: false,
            admin,
            smart_wallet,
            reward_volume: 0
        }
    }

    fn set_paused(&mut self, paused: bool) {
        self.paused = paused;
    }

    fn change_weight(&mut self, weight: u32) {
        self.weight = weight;
    }
}

/// Init function to initialize the staking state
#[init(contract = "gona_stake")]
fn init(ctx: &InitContext, state_builder: &mut StateBuilder) -> InitResult<State> {
    let param: InitParam = ctx.parameter_cursor().get()?;
    Ok(State::empty(
        state_builder,
        param.token_address,
        param.weight,
        param.decimals,
        param.admin,
        param.smart_wallet,
    ))
}

/// The function should be called through the receive hook mechanism of a CIS-2
/// token contract. The function deposits/assigns the sent CIS-2 tokens to a
/// public key.
///
/// The function logs a `DepositCis2Tokens` event.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - the sender is not a contract.
/// - an overflow occurs.
/// - it fails to log the event.
#[receive(
    contract = "gona_stake",
    name = "depositCis2Tokens",
    parameter = "OnReceivingCis2Params<ContractTokenId,ContractTokenAmount>",
    error = "StakingError",
    enable_logger,
    mutable
)]
fn deposit_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
) -> ReceiveResult<()> {
    let cis2_hook_param: OnReceivingCis2Params< 
        ContractTokenId,
        ContractTokenAmount
    > = ctx.parameter_cursor().get()?;

    // Ensures that only contracts can call this hook function.
    let sender_contract_address = match ctx.sender() {
        Address::Contract(sender_contract_address) => sender_contract_address,
        Address::Account(_) => bail!(StakingError::OnlyContractCanStake.into()),
    };

    host
        .state_mut()
        .reward_volume += cis2_hook_param.amount.0;

    logger.log(&Event::DepositCis2Tokens(DepositCis2TokensEvent {
        token_amount: cis2_hook_param.amount,
        token_id: cis2_hook_param.token_id,
        cis2_token_contract_address: sender_contract_address,
        from: cis2_hook_param.from,
    }))?;

    Ok(())
}


#[receive(
    contract = "gona_stake",
    name = "admin_withdraw",
    parameter = "Withdraw",
    error = "StakingError",
    enable_logger,
    mutable
)]
fn admin_withdraw_cis2_tokens(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
) -> ReceiveResult<()> {
    // Parse the parameter.
    let param: Withdraw = ctx.parameter_cursor().get()?;
    let contract_address = host.state.token_address;

    ensure_eq!(
        ctx.sender(),
        host.state.admin,
        StakingError::SenderIsNotAdmin.into()
    );

    // Create Transfer parameter.
    let data: Cis2TransferParameter = TransferParams(vec![concordium_cis2::Transfer {
        token_id: param.token_id.clone(),
        amount: param.withdraw_amount,
        from: Address::Contract(ctx.self_address()),
        to: param.to.clone(),
        data: param.data.clone(),
    }]);

    // Invoke the `transfer` function on the CIS-2 token contract.
    host.invoke_contract(
        &contract_address,
        &data,
        EntrypointName::new_unchecked("transfer"),
        Amount::zero(),
    )?;

    logger.log(&Event::AdminWithdrawCis2Tokens(
        AdminWithdrawCis2TokensEvent {
            token_amount: param.withdraw_amount,
            token_id: param.token_id.clone(),
            cis2_token_contract_address: contract_address,
            from: Address::Contract(ctx.self_address()),
            to: param.to.address(),
        },
    ))?;

    Ok(())
}



#[receive(
    contract = "gona_stake",
    name = "chaperone_stake",
    parameter = "OnReceivingCis2DataParams<ContractTokenId,ContractTokenAmount,PublicKeyEd25519>",
    error = "StakingError",
    enable_logger,
    mutable
)]
fn chaperone_stake(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
) -> ReceiveResult<()> {
    let parameter: OnReceivingCis2DataParams<
        ContractTokenId,
        ContractTokenAmount,
        PublicKeyEd25519,
    > = ctx.parameter_cursor().get()?;
    let amount = parameter.amount;
    let token_id = parameter.token_id;
    let gona_token = host.state().token_address;

    let staker = Staker::Chaperone(parameter.data);


    // Ensures that only contracts can call this hook function.
    let sender_contract_address = match ctx.sender() {
        Address::Contract(sender_contract_address) => sender_contract_address,
        Address::Account(_) => bail!(StakingError::OnlyContractCanStake.into()),
    };
    // Cannot stake less than 0.001 of our token
    ensure!(
        amount.0.ge(&1000),
        StakingError::CannotStakeLessThanAllowAmount.into()
    );
    ensure_eq!(
        sender_contract_address,
        gona_token,
        StakingError::SenderContractAddressIsNotAllowedToStake.into()
    );
    let mut entry = StakeEntry {
        amount,
        time_of_stake: ctx.metadata().block_time(),
        token_id,
    };
    // if let Some(stake_entry) = host.state_mut().stake_entries.remove_and_get(&staker) {
    //     let days_of_stake = ctx
    //         .metadata()
    //         .block_time()
    //         .duration_since(stake_entry.time_of_stake)
    //         .ok_or(StakingError::DaysOfStakeCouldNotBeCalculated)?
    //         .days();
    //     let previous_amount = stake_entry.amount;
    //     let rewards = calculate_percent(previous_amount.0, host.state.weight, host.state.decimals);
    //     if days_of_stake > 0 {
    //         let rewards = rewards * days_of_stake;
    //         let new_amount = previous_amount + TokenAmountU64(rewards);
    //         entry.amount = new_amount;
    //     } else {
    //         entry.amount += previous_amount;
    //     }
    //     host.state_mut()
    //         .stake_entries
    //         .insert(staker, entry)
    //         .ok_or(StakingError::ContractInvokeError)?;
    //     stake_entry.delete();
    // } else {
    //     host.state_mut()
    //         .stake_entries
    //         .insert(staker, entry)
    //         .ok_or(StakingError::ContractInvokeError)?;
    // }
    logger.log(&Event::StakeCis2Tokens(
        DepositCis2TokensEventOfChaperone {
            token_amount: parameter.amount,
            token_id: parameter.token_id.clone(),
            cis2_token_contract_address: gona_token,
            from: parameter.from,
            to: parameter.data,
        },
    ))?;
    Ok(())
}

/// Function to handle staking funds, if staker has some previous staked funds.
/// it calculates the profit, adds it to the current stake and resets the time of stake.
#[receive(
    contract = "gona_stake",
    name = "account_stake",
    parameter = "OnReceivingCis2Params<ContractTokenId,ContractTokenAmount>",
    error = "StakingError",
    enable_logger,
    mutable
)]
fn stake_funds(ctx: &ReceiveContext, host: &mut Host<State>, logger: &mut Logger,
) -> ReceiveResult<()> {
    let parameter: OnReceivingCis2Params<ContractTokenId, ContractTokenAmount> =
        ctx.parameter_cursor().get()?;
    ensure!(!host.state.paused, StakingError::InvalidStakingState.into());
    let amount = parameter.amount;
    let token_id = parameter.token_id;
    let gona_token = host.state().token_address;
    
    let account = match parameter.from {
        Address::Account(account) => account,
        Address::Contract(_) => bail!(StakingError::OnlyContractCanStake.into())
    };

    let staker: Staker = Staker::Account(account);

    // Ensures that only contracts can call this hook function.
    let sender_contract_address = match ctx.sender() {
        Address::Contract(sender_contract_address) => sender_contract_address,
        Address::Account(_) => bail!(StakingError::OnlyContractCanStake.into()),
    };
    // Cannot stake less than 0.001 of our token
    ensure!(
        amount.0.ge(&1000),
        StakingError::CannotStakeLessThanAllowAmount.into()
    );
    ensure_eq!(
        sender_contract_address,
        gona_token,
        StakingError::SenderContractAddressIsNotAllowedToStake.into()
    );
    let mut entry = StakeEntry {
        amount,
        time_of_stake: ctx.metadata().block_time(),
        token_id,
    };
    if let Some(stake_entry) = host.state_mut().stake_entries.remove_and_get(&staker) {
        let days_of_stake = ctx
            .metadata()
            .block_time()
            .duration_since(stake_entry.time_of_stake)
            .ok_or(StakingError::DaysOfStakeCouldNotBeCalculated)?
            .days();
        let previous_amount = stake_entry.amount;
        let rewards = calculate_percent(previous_amount.0, host.state.weight, host.state.decimals);
        if days_of_stake > 0 {
            let rewards = rewards * days_of_stake;
            let new_amount = previous_amount + TokenAmountU64(rewards);
            entry.amount = new_amount;
        } else {
            entry.amount += previous_amount;
        }
        host.state_mut()
            .stake_entries
            .insert(staker, entry)
            .ok_or(StakingError::ContractInvokeError)?;
        stake_entry.delete();
    } else {
        host.state_mut()
            .stake_entries
            .insert(staker, entry)
            .ok_or(StakingError::ContractInvokeError)?;
    }
    logger.log(&Event::AccountStakeCis2Tokens(
        DepositCis2TokensAccountEvent {
            token_amount: parameter.amount,
            token_id: parameter.token_id.clone(),
            cis2_token_contract_address: gona_token,
            from: Address::Contract(ctx.self_address()),
            to: account,
        },
    ))?;
    Ok(())
}

/// calculate the reward of the stake for the current season.
/// the calculate is done using the decimals of the token.
/// this fn assumes that the amount and weight is `n * 10.pow(decimals)`
fn calculate_percent(amount: u64, weight: u32, decimals: u8) -> u64 {
    (amount * (weight as u64)) / (100 * (10_i32.pow(decimals as u32) as u64))
}
//Function to release the staked funds
#[receive(
    contract = "gona_stake",
    name = "withdraw_stake",
    parameter = "WithdrawStake",
    mutable,
    enable_logger,
    crypto_primitives
)]
fn release_funds(
    ctx: &ReceiveContext,
    host: &mut Host<State>,
    logger: &mut Logger,
    crypto_primitives: &impl HasCryptoPrimitives,
) ->  ReceiveResult<()> {
    let param: WithdrawStake = ctx.parameter_cursor().get()?;
    // let owner = Address::Account(AccountAddress::from_str(ctx.sender()).unwrap());
    let token_address = host.state.token_address;
    let smart_wallet = host.state.smart_wallet;
    ensure!(!host.state.paused, StakingError::InvalidStakingState.into());
    match &param.owner {
        Staker::Account(owner) => {
            ensure_eq!(
                ctx.sender(),
                Address::Account(owner.to_owned()),
                StakingError::SenderIsNotOwner.into()
            );
            let stake_entry = host
                .state()
                .stake_entries
                .get(&param.owner)
                .ok_or(StakingError::StakingNotFound)?;
            let previous_amount = stake_entry.amount;
            ensure!(
                previous_amount.0.ge(&param.amount.0),
                StakingError::InsufficientFunds.into()
            );
            let days_of_stake = ctx
                .metadata()
                .block_time()
                .duration_since(stake_entry.time_of_stake)
                .ok_or(StakingError::DaysOfStakeCouldNotBeCalculated)?
                .minutes();

            let mut amount = param.amount;
            let rewards = calculate_percent(amount.0, host.state.weight, host.state.decimals);
            // if days == 0 and you calculate reward. it will change balance to 0
            if days_of_stake > 0 {
                let rewards = rewards * days_of_stake;
            let reward_volume = host.state.reward_volume;
            ensure!(reward_volume >= rewards,StakingError::Overflow.into());
                host.state.reward_volume -= rewards;
                amount += TokenAmountU64(rewards);
            }

            // Create a Transfer instance
            let transfer_payload = Transfer {
                token_id: param.token_id,
                amount,
                to: Receiver::Account(owner.to_owned()),
                from: Address::Contract(ctx.self_address()),
                data: AdditionalData::empty(),
            };
            let entry_point = EntrypointName::new_unchecked("transfer".into());

            let mut transfers = Vec::new();
            transfers.push(transfer_payload);
            let payload = TransferParams::from(transfers);
            let balance = previous_amount.0 - param.amount.0;

            if balance < 1000 {
                host.state.stake_entries.remove(&param.owner);
            } else {
                host.state
                    .stake_entries
                    .entry(param.owner.clone())
                    .and_modify(|stake| {
                        stake.amount = TokenAmountU64(balance);
                    });
            }
            host.invoke_contract(&token_address, &payload, entry_point, Amount::zero())?;
            logger.log(&Event::UnstakeCis2Tokens(
                UnstakeCis2TokensEvent {
                    token_amount: param.amount,
                    token_id: param.token_id.clone(),
                    cis2_token_contract_address: token_address,
                    to: Address::Account(*owner),
                },
            ))?;
            Ok(())
        }
        Staker::Chaperone(chaperone) => {
            let Payload {
                signer,
                signature,
                message,
            } = param
                .additional_data
                .ok_or(StakingError::CouldNotParseAdditionalData)?;
            let WithdrawStakeForChaperone {
                expiry_time: _,
                owner,
                token_id,
                amount,
                entry_point,
            } = message.clone();
            ensure!(
                signer.cmp(&chaperone) == cmp::Ordering::Equal,
                StakingError::WrongSignature.into()
            );
            validate_signature(&message, signer, signature, crypto_primitives, ctx)?;
            let stake_entry = host
                .state()
                .stake_entries
                .get(&owner)
                .ok_or(StakingError::StakingNotFound)?;

            let previous_amount = stake_entry.amount;
            ensure!(
                previous_amount.0.ge(&param.amount.0),
                StakingError::InsufficientFunds.into()
            );
            let days_of_stake = ctx
                .metadata()
                .block_time()
                .duration_since(stake_entry.time_of_stake)
                .ok_or(StakingError::DaysOfStakeCouldNotBeCalculated)?
                .minutes();  // change this 

            let mut amount = amount;
            let rewards = calculate_percent(amount.0, host.state.weight, host.state.decimals);
            // if days == 0 and you calculate reward. it will change balance to 0
            if days_of_stake > 0 {
                let rewards = rewards * days_of_stake;
                let reward_volume = host.state.reward_volume;
                ensure!(reward_volume >= rewards, StakingError::Overflow.into());
                host.state.reward_volume -= rewards;
                amount += TokenAmountU64(rewards);
            }
            let owned_entry = OwnedEntrypointName::new(entry_point)
                .expect("This is a legit string; this should not have happend");
            // Create a Transfer instance
            let transfer_payload = Transfer {
                token_id,
                amount,
                to: Receiver::Contract(smart_wallet, owned_entry),
                from: Address::Contract(ctx.self_address()),
                data: AdditionalData::from(to_bytes(&chaperone)),
            };
            let entry_point = EntrypointName::new_unchecked("transfer".into());

            let mut transfers = Vec::new();
            transfers.push(transfer_payload);
            let payload = TransferParams::from(transfers);
            let balance = previous_amount.0 - param.amount.0;

            if balance < 1000 {
                host.state.stake_entries.remove(&param.owner);
            } else {
                host.state
                    .stake_entries
                    .entry(param.owner.clone())
                    .and_modify(|stake| {
                        stake.amount = TokenAmountU64(balance);
                    });
            }
            host.invoke_contract(&token_address, &payload, entry_point, Amount::zero())?;
            logger.log(&Event::UnstakeCis2TokensOfChaperone(
                UnstakeCis2TokensEventOfChaperone {
                    token_amount: param.amount,
                    token_id: param.token_id.clone(),
                    cis2_token_contract_address: token_address,
                    smart_wallet,
                    key: chaperone.clone()
                },
            ))?;
            Ok(())
        }
    }
}

/// Function to get stake information by ID
#[receive(
    contract = "gona_stake",
    name = "get_stake_info",
    parameter = "Staker",
    return_value = "Option<StakeEntry>"
)]
fn get_stake_info(ctx: &ReceiveContext, host: &Host<State>) -> ReceiveResult<Option<StakeEntry>> {
    let param: Staker = ctx.parameter_cursor().get()?;
    let stake_entry_ref = host.state().stake_entries.get(&param);
    // Convert the StateRef to Option<StakeEntry>
    let stake_entry_option = stake_entry_ref.map(|entry_ref| entry_ref.to_owned());
    Ok(stake_entry_option)
}

/// Function to get stake information by ID
#[receive(contract = "gona_stake", name = "set_paused", mutable)]
fn set_paused(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    ensure_eq!(
        ctx.sender(),
        host.state.admin,
        StakingError::SenderIsNotAdmin.into()
    );
    host.state_mut().set_paused(true);

    Ok(())
}

/// Function to get stake information by ID
#[receive(contract = "gona_stake", name = "change_weight",     parameter = "u32",
mutable)]
fn change_weight(ctx: &ReceiveContext, host: &mut Host<State>) -> ReceiveResult<()> {
    let weight: u32 = ctx.parameter_cursor().get()?;
    ensure_eq!(
        ctx.sender(),
        host.state.admin,
        StakingError::SenderIsNotAdmin.into()
    );
    host.state_mut().change_weight(weight);

    Ok(())
}

//function to upgrade contract
#[receive(
    contract = "gona_stake",
    name = "upgrade",
    parameter = "UpgradeParams",
    low_level
)]
fn contract_upgrade(ctx: &ReceiveContext, host: &mut LowLevelHost) -> ReceiveResult<()> {
    // Check that only the owner is authorized to upgrade the smart contract.
    ensure!(ctx.sender().matches_account(&ctx.owner()));
    // Parse the parameter.
    let params: UpgradeParams = ctx.parameter_cursor().get()?;
    // Trigger the upgrade.
    host.upgrade(params.module)?;
    // Call the migration function if provided.
    if let Some((func, parameters)) = params.migrate {
        host.invoke_contract_raw(
            &ctx.self_address(),
            parameters.as_parameter(),
            func.as_entrypoint_name(),
            Amount::zero(),
        )?;
    }
    Ok(())
}

/// Helper function to calculate the `MessageHash` for a withdrawal.
#[receive(
    contract = "gona_stake",
    name = "get_param_hash",
    parameter = "WithdrawStake",
    return_value = "[u8;32]",
    error = "StakingError",
    crypto_primitives,
    mutable
)]
fn contract_get_register_message_hash(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
    crypto_primitives: &impl HasCryptoPrimitives,
) -> Result<[u8; 32], StakingError> {
    // Parse the parameter.
    let param: WithdrawStakeForChaperone = ctx.parameter_cursor().get()?;
    calculate_message_hash_from_bytes(&to_bytes(&param), crypto_primitives, ctx)
}

/// It rejects if:
/// - the message is expired.
/// - the signature is invalid.
/// - the message hash can not be calculated.
fn validate_signature<T: Serial + IsMessage>(
    message: &T,
    signer: PublicKeyEd25519,
    signature: SignatureEd25519,
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> Result<(), StakingError> {
    // Check that the signature is not expired.
    ensure!(
        message.expiry_time() > ctx.metadata().slot_time(),
        StakingError::Expired.into()
    );
    // Calculate the message hash.
    let message_hash: [u8; 32] =
        calculate_message_hash_from_bytes(&to_bytes(&message), crypto_primitives, ctx)?;
    // Check the signature.
    let valid_signature =
        crypto_primitives.verify_ed25519_signature(signer, signature, &message_hash);
    ensure!(valid_signature, StakingError::WrongSignature.into());

    Ok(())
}

/// Calculates the message hash from the message bytes.
/// It prepends the message bytes with a context string consisting of the
/// `genesis_hash` and this contract address.
fn calculate_message_hash_from_bytes(
    message_bytes: &[u8],
    crypto_primitives: &impl HasCryptoPrimitives,
    ctx: &ReceiveContext,
) -> Result<[u8; 32], StakingError> {
    // We prepend the message with a context string consistent of the genesis_hash
    // and this contract address.
    let mut msg_prepend = [0; 32 + 16];
    msg_prepend[0..32].copy_from_slice(TESTNET_GENESIS_HASH.as_ref());
    msg_prepend[32..40].copy_from_slice(&ctx.self_address().index.to_le_bytes());
    msg_prepend[40..48].copy_from_slice(&ctx.self_address().subindex.to_le_bytes());

    // Calculate the message hash.
    Ok(crypto_primitives
        .hash_sha2_256(&[&msg_prepend[0..48], &message_bytes].concat())
        .0)
}



/// The function should be called through the receive hook mechanism of a CIS-2
/// token contract. The function deposits/assigns the sent CIS-2 tokens to a
/// public key.
///
/// The function logs a `DepositCis2Tokens` event.
///
/// It rejects if:
/// - it fails to parse the parameter.
/// - the sender is not a contract.
/// - an overflow occurs.
/// - it fails to log the event.
#[receive(
    contract = "gona_stake",
    name = "depositTokens",
    parameter = "OnReceivingCis2DataParams<ContractTokenId,ContractTokenAmount,PublicKeyEd25519>",
    error = "StakingError",
    mutable
)]
fn cis2_tokens(
    ctx: &ReceiveContext,
    _host: &mut Host<State>,
) -> ReceiveResult<()> {
    let _cis2_hook_param: OnReceivingCis2DataParams<
        ContractTokenId,
        ContractTokenAmount,
        PublicKeyEd25519,
    > = ctx.parameter_cursor().get()?;   
    Ok(())
}