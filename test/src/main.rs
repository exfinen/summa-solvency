#![feature(generic_const_exprs)]

use std::{
    fs::File,
    io::Write,
    io::BufReader,
};
use ethers::{
    prelude::abigen,
    providers::Provider,
    types::{
        U256, 
        Address,
    },
};
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
};
use std::sync::Arc;
use summa_solvency::merkle_sum_tree::MerkleSumTree;

abigen!(
    ISummaContract,
    "../backend/src/contracts/abi/Summa.json",
);

abigen!(
    IInclusionVerifier,
    "../backend/src/contracts/abi/InclusionVerifier.json",
);

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

    let summa_addr: Address =
        "0xe7f1725E7734CE288F8367e1Bb143E90bb3F0512".parse()?;

    let signer = {
        // Account #0 private key
        let priv_key_0 = "0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80";
        let rpc_endpoint = "http://localhost:8545";

        SummaSigner::new(
            priv_key_0,
            rpc_endpoint,
            AddressInput::Address(summa_addr),
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

    let summa_contract = {
        let provider = {
            let rpc_url = "http://localhost:8545";
            Arc::new(Provider::try_from(rpc_url)?)
        };
        ISummaContract::new(
            summa_addr,
            provider,
        )
    };

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
        ).await?
    };
    println!("Is proof valid? {:?}", is_incl_proof_valid);

    Ok(())
}

#[tokio::main]
async fn main() {
    run_test().await.unwrap();
}

