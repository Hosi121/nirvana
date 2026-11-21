//! verification integration suite.
#[path = "support"]
mod support {
    pub mod ir;
    pub mod rewrite_cases;
}

#[path = "verification/block_verification.rs"]
mod block_verification;
#[path = "verification/exhaustive.rs"]
mod exhaustive;
#[path = "verification/recovery_verification.rs"]
mod recovery_verification;
#[path = "verification/verification.rs"]
mod verification;
