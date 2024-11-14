use crate::*;
/// Trait definition of the `IsMessage`. This trait is implemented for the two
/// types `WithdrawMessage` and `TransferMessage`. The `isMessage` trait is used
/// as an input parameter to the `validate_signature_and_increase_nonce`
/// function so that the function works with both message types.
pub trait IsMessage {
    fn expiry_time(&self) -> Timestamp;
}

/// Tagged events to be serialized for the event log.
#[derive(Debug, Serial, Deserial, PartialEq, Eq, SchemaType)]
#[concordium(repr(u8))]
pub enum Event {
    #[concordium(tag = 246)]
    UnstakeCis2TokensOfChaperone(UnstakeCis2TokensEventOfChaperone),

    #[concordium(tag = 245)]
    UnstakeCis2Tokens(UnstakeCis2TokensEvent),

    #[concordium(tag = 244)]
    DepositCis2Tokens(DepositCis2TokensEvent),

    #[concordium(tag = 243)]
    AdminWithdrawCis2Tokens(AdminWithdrawCis2TokensEvent),

    #[concordium(tag = 242)]
    StakeCis2Tokens(DepositCis2TokensEventOfChaperone),

    #[concordium(tag = 241)]
    AccountStakeCis2Tokens(DepositCis2TokensAccountEvent),
}

/// The `DepositCcdEvent` is logged whenever a CCD amount received by

/// The `DepositCis2TokensEvent` is logged whenever a token amount received by
/// the contract is assigned to a public key.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositCis2TokensEvent {
    /// The token amount assigned to a public key.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token deposit.
    pub token_id: ContractTokenId,
    /// The token contract address of the token deposit.
    pub cis2_token_contract_address: ContractAddress,
    /// The address that invoked the deposit entrypoint.
    pub from: Address,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositCis2TokensAccountEvent {
    /// The token amount assigned to a public key.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token deposit.
    pub token_id: ContractTokenId,
    /// The token contract address of the token deposit.
    pub cis2_token_contract_address: ContractAddress,
    /// The address that invoked the deposit entrypoint.
    pub from: Address,
    /// The public key that the CCD amount is assigned to.
    pub to: AccountAddress,
}

#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositCis2TokensEventOfChaperone {
    /// The token amount assigned to a public key.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token deposit.
    pub token_id: ContractTokenId,
    /// The token contract address of the token deposit.
    pub cis2_token_contract_address: ContractAddress,
    /// The address that invoked the deposit entrypoint.
    pub from: Address,
    /// The public key that the CCD amount is assigned to.
    pub to: PublicKeyEd25519,
}

/// The `WithdrawCis2TokensEvent` is logged whenever a token amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct WithdrawCis2TokensEvent {
    /// The token amount withdrawn.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token withdrawn.
    pub token_id: ContractTokenId,
    /// The token contract address of the token withdrawn.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key that the token amount will be withdrawn from.
    pub from: PublicKeyEd25519,
    /// The address that the token amount is withdrawn to.
    pub to: Address,
}

/// The `WithdrawCis2TokensEvent` is logged whenever a token amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct UnstakeCis2TokensEvent {
    /// The token amount withdrawn.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token withdrawn.
    pub token_id: ContractTokenId,
    /// The token contract address of the token withdrawn.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key that the token amount will be withdrawn from.
    pub to: Address,
}

/// The `WithdrawCis2TokensEvent` is logged whenever a token amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct UnstakeCis2TokensEventOfChaperone {
    /// The token amount withdrawn.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token withdrawn.
    pub token_id: ContractTokenId,
    /// The token contract address of the token withdrawn.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key that the token amount will be withdrawn from.
    pub smart_wallet: ContractAddress,

    pub key: PublicKeyEd25519,
}

/// The `WithdrawCis2TokensEvent` is logged whenever a token amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct AdminWithdrawCis2TokensEvent {
    /// The token amount withdrawn.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token withdrawn.
    pub token_id: ContractTokenId,
    /// The token contract address of the token withdrawn.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key that the token amount will be withdrawn from.
    pub from: Address,
    /// The address that the token amount is withdrawn to.
    pub to: Address,
}
