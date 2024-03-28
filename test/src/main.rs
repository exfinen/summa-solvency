#![feature(generic_const_exprs)]

use std::{
    fs::File,
    io::Write,
    io::BufReader,
};
use ethers::types::U256;
use serde_json::{
    from_reader,
    to_string_pretty,
};
use summa_backend::{
    apis::{
        address_ownership::AddressOwnership,
        leaf_hash_from_inputs,
        round::{MstInclusionProof, Round},
    },
    contracts::signer::{AddressInput, SummaSigner},
    tests::initialize_test_env,
};
use summa_solvency::merkle_sum_tree::MerkleSumTree;

async fn run_test() -> Result<(), Box<dyn std::error::Error>> {
    // What to prove
    const BOB_INDEX: usize = 1;
    const SNAPSHOT_TIME: u64 = 1;
    let user_name = "bob".to_string();
    let balances = vec!["50".to_string()];

    // MST to use
    const N_CURRENCIES: usize = 1;
    const LEVELS: usize = 2;
    const N_BYTES: usize = 2;

    let (_, _, _, _, summa_contract) = initialize_test_env(None).await;

    let signer = {
        // Account #18
        SummaSigner::new(
            "0xde9be858da4a475276426320d5e9262ecfc3ba460bfac56360bfa6c4c28b4ee0",
            "http://localhost:8545/",
            AddressInput::Address(summa_contract.address()),
        )
        .await?
     };

    // Generate address ownership proof and
    // send to the contract
    {
        let mut addr_ownership_cli = AddressOwnership::new(
            &signer,
            "./input/sig.csv",
        ).unwrap();

        addr_ownership_cli
            .dispatch_proof_of_address_ownership()
            .await?; 
        println!("Sent address ownership proof to the contract");
    }

    let mut round = {
        let ptau = "./input/hermez-raw-11";
        let entry = "./input/entry.csv";
        let mst = MerkleSumTree::from_csv(entry).unwrap();

        Round::<LEVELS, N_CURRENCIES, N_BYTES>::new(
            &signer,
            Box::new(mst),
            ptau,
            SNAPSHOT_TIME,
        ).unwrap()
    };

    // Generate liabilities commitment and
    // send to the contract
    round.dispatch_commitment().await?;
    println!("Sent liabilities commitment to the contract");

    // Generate inclusion proof and write to a file
    let incl_proof_file = {
        let incl_proof =
            round.get_proof_of_inclusion(BOB_INDEX).unwrap();
        println!("Generated inclusion proof");

        let file_name = "incl_proof.json";
        let mut file = File::create(file_name).unwrap();
        let output = to_string_pretty(&incl_proof).unwrap();
        file.write_all(output.as_bytes())
            .expect("Failed to write JSON to file");

        println!("Saved proof to `{}`", file_name);
        file_name
    };

    //  load inclusion proof from the file
    let incl_proof: MstInclusionProof = {
        let file = File::open(incl_proof_file)?;
        let reader = BufReader::new(file);
        from_reader(reader)?
    };
    println!("Loaded inclusion proof from {}`", incl_proof_file);

    // get public inputs from the proof
    let public_inputs = incl_proof.get_public_inputs();

    // confirm that leaf hash in the public inputs is valid
    {
        let leaf_hash = public_inputs[0];
        assert_eq!(leaf_hash,
            leaf_hash_from_inputs::<N_CURRENCIES>(
                user_name.clone(),
                balances.clone(),
            )
        );
        println!("Leaf hash is valid");
    }

    // Get the MST root at SNAPSHOT_TIME from the contract
    let snapshot_time = U256::from(SNAPSHOT_TIME);
    let mst_root_commitment = summa_contract
        .commitments(snapshot_time)
        .call()
        .await?;
    println!("Got MST root commitment from the contract");

    // confirm the commitment matches with
    // the one in public inputs
    assert_eq!(mst_root_commitment, public_inputs[1]);
    println!("MST root commitment is valid");

    // Validate inclusion proof with the contract verifier
    let is_incl_proof_valid = {
        summa_contract.verify_inclusion_proof(
            incl_proof.get_proof().clone(),
            public_inputs.clone(),
            snapshot_time
        ).await?;
    };
    println!("Is proof valid? {:?}", is_incl_proof_valid);

    Ok(())
}

#[tokio::main]
async fn main() {
    run_test().await.unwrap();
}

