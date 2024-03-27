#![feature(generic_const_exprs)]

use std::{
    fs::File,
    io::Write,
};
use serde_json::to_string_pretty;
use summa_backend::{
    apis::{
        address_ownership::AddressOwnership,
        round::Round,
    },
    contracts::signer::{AddressInput, SummaSigner},
    tests::initialize_test_env,
};
use summa_solvency::merkle_sum_tree::MerkleSumTree;

async fn run_test() -> Result<(), Box<dyn std::error::Error>> {
    let (_, _, _, _, summa_contract) = initialize_test_env(None).await;

    // Address ownership proof

    // Account #19
    // let priv_key = "0xdf57089febbacf7ba0bc227dafbffa9fc08a93fdc68e1e42411a14efcf23656e";

    // Account #18
    let priv_key = "0xde9be858da4a475276426320d5e9262ecfc3ba460bfac56360bfa6c4c28b4ee0";

    let signer = SummaSigner::new(
        priv_key,
        "http://127.0.0.1:8545",
        AddressInput::Address(summa_contract.address()),
    )
    .await?;

    let sig_csv_path = "./input/sig.csv";

    let mut addr_ownership_cli =
        AddressOwnership::new(
            &signer,
            sig_csv_path,
        ).unwrap();

    addr_ownership_cli
        .dispatch_proof_of_address_ownership()
        .await?; 

    // Liabilities commitment

    let ptau = "./input/hermez-raw-11";
    let entry = "./input/entry.csv";
    let mst = MerkleSumTree::from_csv(entry).unwrap();

    let timestamp = 1u64;
    let mut round = Round::<2, 1, 2>::new(
        &signer,
        Box::new(mst),
        ptau,
        timestamp,
    ).unwrap();

    round.dispatch_commitment().await?;

    // Inclusion proof
    let bob_index = 1;
    let inclusion_proof = round.get_proof_of_inclusion(bob_index).unwrap();
    println!("Got proof: {:?}", &inclusion_proof);

    let file_name = "bob_proof.json";
    let mut file = File::create(file_name).unwrap();
    let output = to_string_pretty(&inclusion_proof).unwrap();
    file.write_all(output.as_bytes())
        .expect("Failed to write JSON to file");

    println!("Saved proof to `{}`", file_name);

    Ok(())
}

#[tokio::main]
async fn main() {
    run_test().await.unwrap();
}

