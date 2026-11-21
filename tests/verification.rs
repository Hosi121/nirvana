//! verification integration suite.
#[allow(dead_code)]
mod support;

#[path = "verification/block_verification.rs"]
mod block_verification;
#[path = "verification/exhaustive.rs"]
mod exhaustive;
#[path = "verification/recovery_verification.rs"]
mod recovery_verification;
#[path = "verification/verification.rs"]
mod verification;
