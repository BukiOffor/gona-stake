use concordium_std::Timestamp;

/// Trait definition of the `IsMessage`. This trait is implemented for the two
/// types `WithdrawMessage` and `TransferMessage`. The `isMessage` trait is used
/// as an input parameter to the `validate_signature_and_increase_nonce`
/// function so that the function works with both message types.
pub trait IsMessage {
    fn expiry_time(&self) -> Timestamp;
}

