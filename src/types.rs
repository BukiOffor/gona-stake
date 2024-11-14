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
    /// The event tracks the nonce used in the message that was signed.
    #[concordium(tag = 250)]
    Nonce(NonceEvent),
    /// The event tracks every time a CCD amount received by the contract is
    /// assigned to a public key.
    #[concordium(tag = 249)]
    DepositCcd(DepositCcdEvent),
    /// The event tracks every time a token amount received by the contract is
    /// assigned to a public key.
    #[concordium(tag = 248)]
    DepositCis2Tokens(DepositCis2TokensEvent),
    /// The event tracks every time a CCD amount held by a public key is
    /// withdrawn to an address.
    #[concordium(tag = 247)]
    WithdrawCcd(WithdrawCcdEvent),
    /// The event tracks every time a token amount held by a public key is
    /// withdrawn to an address.
    #[concordium(tag = 246)]
    WithdrawCis2Tokens(WithdrawCis2TokensEvent),
    /// The event tracks every time a CCD amount held by a public key is
    /// transferred to another public key within the contract.
    #[concordium(tag = 245)]
    TransferCcd(TransferCcdEvent),
    /// The event tracks every time a token amount held by a public key is
    /// transferred to another public key within the contract.
    #[concordium(tag = 244)]
    TransferCis2Tokens(TransferCis2TokensEvent),

    #[concordium(tag = 243)]
    AdminWithdrawCis2Tokens(AdminWithdrawCis2TokensEvent),
}

/// The `NonceEvent` is logged whenever a signature is checked. The event
/// tracks the nonce used by the signer of the message.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct NonceEvent {
    /// The nonce that was used in the message.
    pub nonce: u64,
    /// Account that signed the message.
    pub public_key: PublicKeyEd25519,
}

/// The `DepositCcdEvent` is logged whenever a CCD amount received by
/// the contract is assigned to a public key.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct DepositCcdEvent {
    /// The CCD amount assigned to a public key.
    pub ccd_amount: Amount,
    /// The address that invoked the deposit entrypoint.
    pub from: Address,
    /// The public key that the CCD amount is assigned to.
    pub to: PublicKeyEd25519,
}

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
    /// The public key that the CCD amount is assigned to.
    pub to: PublicKeyEd25519,
}

/// The `WithdrawCcdEvent` is logged whenever a CCD amount held by a
/// public key is withdrawn to an address.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct WithdrawCcdEvent {
    /// The CCD amount withdrawn.
    pub ccd_amount: Amount,
    /// The public key that the CCD amount will be withdrawn from.
    pub from: PublicKeyEd25519,
    /// The address that the CCD amount is withdrawn to.
    pub to: Address,
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

/// The `TransferCcdEvent` is logged whenever a CCD amount
/// held by a public key is transferred to another public key within the
/// contract.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct TransferCcdEvent {
    /// The CCD amount transferred.
    pub ccd_amount: Amount,
    /// The public key that the CCD amount will be transferred from.
    pub from: PublicKeyEd25519,
    /// The public key that the CCD amount is transferred to.
    pub to: PublicKeyEd25519,
}

/// The `TransferCis2TokensEvent` is logged whenever a token amount held
/// by a public key is transferred to another public key within the contract.
#[derive(Debug, Serialize, SchemaType, PartialEq, Eq)]
pub struct TransferCis2TokensEvent {
    /// The token amount transferred.
    pub token_amount: ContractTokenAmount,
    /// The token id of the token transferred.
    pub token_id: ContractTokenId,
    /// The token contract address of the token transferred.
    pub cis2_token_contract_address: ContractAddress,
    /// The public key that the token amount will be transferred from.
    pub from: PublicKeyEd25519,
    /// The public key that the token amount is transferred to.
    pub to: PublicKeyEd25519,
}
