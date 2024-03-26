pub use summa::*;
/// This module was auto-generated with ethers-rs Abigen.
/// More information at: <https://github.com/gakonst/ethers-rs>
#[allow(
    clippy::enum_variant_names,
    clippy::too_many_arguments,
    clippy::upper_case_acronyms,
    clippy::type_complexity,
    dead_code,
    non_camel_case_types,
)]
pub mod summa {
    #[allow(deprecated)]
    fn __abi() -> ::ethers::core::abi::Abi {
        ::ethers::core::abi::ethabi::Contract {
            constructor: ::core::option::Option::Some(::ethers::core::abi::ethabi::Constructor {
                inputs: ::std::vec![
                    ::ethers::core::abi::ethabi::Param {
                        name: ::std::borrow::ToOwned::to_owned("_inclusionVerifier"),
                        kind: ::ethers::core::abi::ethabi::ParamType::Address,
                        internal_type: ::core::option::Option::Some(
                            ::std::borrow::ToOwned::to_owned("contract IVerifier"),
                        ),
                    },
                    ::ethers::core::abi::ethabi::Param {
                        name: ::std::borrow::ToOwned::to_owned("mstLevels"),
                        kind: ::ethers::core::abi::ethabi::ParamType::Uint(16usize),
                        internal_type: ::core::option::Option::Some(
                            ::std::borrow::ToOwned::to_owned("uint16"),
                        ),
                    },
                    ::ethers::core::abi::ethabi::Param {
                        name: ::std::borrow::ToOwned::to_owned("currenciesCount"),
                        kind: ::ethers::core::abi::ethabi::ParamType::Uint(16usize),
                        internal_type: ::core::option::Option::Some(
                            ::std::borrow::ToOwned::to_owned("uint16"),
                        ),
                    },
                    ::ethers::core::abi::ethabi::Param {
                        name: ::std::borrow::ToOwned::to_owned("balanceByteRange"),
                        kind: ::ethers::core::abi::ethabi::ParamType::Uint(8usize),
                        internal_type: ::core::option::Option::Some(
                            ::std::borrow::ToOwned::to_owned("uint8"),
                        ),
                    },
                ],
            }),
            functions: ::core::convert::From::from([
                (
                    ::std::borrow::ToOwned::to_owned("addressOwnershipProofs"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned(
                                "addressOwnershipProofs",
                            ),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::string::String::new(),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256"),
                                    ),
                                },
                            ],
                            outputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("cexAddress"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::String,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("string"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("chain"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::String,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("string"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("signature"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Bytes,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("bytes"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("message"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Bytes,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("bytes"),
                                    ),
                                },
                            ],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::View,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("commitments"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned("commitments"),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::string::String::new(),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256"),
                                    ),
                                },
                            ],
                            outputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("mstRoot"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256"),
                                    ),
                                },
                            ],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::View,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("config"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned("config"),
                            inputs: ::std::vec![],
                            outputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("mstLevels"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(16usize),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint16"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("currenciesCount"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(16usize),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint16"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("balanceByteRange"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(8usize),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint8"),
                                    ),
                                },
                            ],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::View,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("getAddressOwnershipProof"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned(
                                "getAddressOwnershipProof",
                            ),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("addressHash"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::FixedBytes(
                                        32usize,
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("bytes32"),
                                    ),
                                },
                            ],
                            outputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::string::String::new(),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Tuple(
                                        ::std::vec![
                                            ::ethers::core::abi::ethabi::ParamType::String,
                                            ::ethers::core::abi::ethabi::ParamType::String,
                                            ::ethers::core::abi::ethabi::ParamType::Bytes,
                                            ::ethers::core::abi::ethabi::ParamType::Bytes,
                                        ],
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned(
                                            "struct Summa.AddressOwnershipProof",
                                        ),
                                    ),
                                },
                            ],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::View,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("owner"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned("owner"),
                            inputs: ::std::vec![],
                            outputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::string::String::new(),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Address,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("address"),
                                    ),
                                },
                            ],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::View,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("renounceOwnership"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned("renounceOwnership"),
                            inputs: ::std::vec![],
                            outputs: ::std::vec![],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::NonPayable,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("submitCommitment"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned("submitCommitment"),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("mstRoot"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("rootBalances"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Array(
                                        ::std::boxed::Box::new(
                                            ::ethers::core::abi::ethabi::ParamType::Uint(256usize),
                                        ),
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256[]"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("cryptocurrencies"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Array(
                                        ::std::boxed::Box::new(
                                            ::ethers::core::abi::ethabi::ParamType::Tuple(
                                                ::std::vec![
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                ],
                                            ),
                                        ),
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned(
                                            "struct Summa.Cryptocurrency[]",
                                        ),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("timestamp"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256"),
                                    ),
                                },
                            ],
                            outputs: ::std::vec![],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::NonPayable,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("submitProofOfAddressOwnership"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned(
                                "submitProofOfAddressOwnership",
                            ),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned(
                                        "_addressOwnershipProofs",
                                    ),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Array(
                                        ::std::boxed::Box::new(
                                            ::ethers::core::abi::ethabi::ParamType::Tuple(
                                                ::std::vec![
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                    ::ethers::core::abi::ethabi::ParamType::Bytes,
                                                    ::ethers::core::abi::ethabi::ParamType::Bytes,
                                                ],
                                            ),
                                        ),
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned(
                                            "struct Summa.AddressOwnershipProof[]",
                                        ),
                                    ),
                                },
                            ],
                            outputs: ::std::vec![],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::NonPayable,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("transferOwnership"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned("transferOwnership"),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("newOwner"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Address,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("address"),
                                    ),
                                },
                            ],
                            outputs: ::std::vec![],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::NonPayable,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("verifyInclusionProof"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Function {
                            name: ::std::borrow::ToOwned::to_owned(
                                "verifyInclusionProof",
                            ),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("proof"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Bytes,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("bytes"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("publicInputs"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Array(
                                        ::std::boxed::Box::new(
                                            ::ethers::core::abi::ethabi::ParamType::Uint(256usize),
                                        ),
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256[]"),
                                    ),
                                },
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::borrow::ToOwned::to_owned("timestamp"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("uint256"),
                                    ),
                                },
                            ],
                            outputs: ::std::vec![
                                ::ethers::core::abi::ethabi::Param {
                                    name: ::std::string::String::new(),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Bool,
                                    internal_type: ::core::option::Option::Some(
                                        ::std::borrow::ToOwned::to_owned("bool"),
                                    ),
                                },
                            ],
                            constant: ::core::option::Option::None,
                            state_mutability: ::ethers::core::abi::ethabi::StateMutability::View,
                        },
                    ],
                ),
            ]),
            events: ::core::convert::From::from([
                (
                    ::std::borrow::ToOwned::to_owned("AddressOwnershipProofSubmitted"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Event {
                            name: ::std::borrow::ToOwned::to_owned(
                                "AddressOwnershipProofSubmitted",
                            ),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::EventParam {
                                    name: ::std::borrow::ToOwned::to_owned(
                                        "addressOwnershipProofs",
                                    ),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Array(
                                        ::std::boxed::Box::new(
                                            ::ethers::core::abi::ethabi::ParamType::Tuple(
                                                ::std::vec![
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                    ::ethers::core::abi::ethabi::ParamType::Bytes,
                                                    ::ethers::core::abi::ethabi::ParamType::Bytes,
                                                ],
                                            ),
                                        ),
                                    ),
                                    indexed: false,
                                },
                            ],
                            anonymous: false,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("LiabilitiesCommitmentSubmitted"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Event {
                            name: ::std::borrow::ToOwned::to_owned(
                                "LiabilitiesCommitmentSubmitted",
                            ),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::EventParam {
                                    name: ::std::borrow::ToOwned::to_owned("timestamp"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    indexed: true,
                                },
                                ::ethers::core::abi::ethabi::EventParam {
                                    name: ::std::borrow::ToOwned::to_owned("mstRoot"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Uint(
                                        256usize,
                                    ),
                                    indexed: false,
                                },
                                ::ethers::core::abi::ethabi::EventParam {
                                    name: ::std::borrow::ToOwned::to_owned("rootBalances"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Array(
                                        ::std::boxed::Box::new(
                                            ::ethers::core::abi::ethabi::ParamType::Uint(256usize),
                                        ),
                                    ),
                                    indexed: false,
                                },
                                ::ethers::core::abi::ethabi::EventParam {
                                    name: ::std::borrow::ToOwned::to_owned("cryptocurrencies"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Array(
                                        ::std::boxed::Box::new(
                                            ::ethers::core::abi::ethabi::ParamType::Tuple(
                                                ::std::vec![
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                    ::ethers::core::abi::ethabi::ParamType::String,
                                                ],
                                            ),
                                        ),
                                    ),
                                    indexed: false,
                                },
                            ],
                            anonymous: false,
                        },
                    ],
                ),
                (
                    ::std::borrow::ToOwned::to_owned("OwnershipTransferred"),
                    ::std::vec![
                        ::ethers::core::abi::ethabi::Event {
                            name: ::std::borrow::ToOwned::to_owned(
                                "OwnershipTransferred",
                            ),
                            inputs: ::std::vec![
                                ::ethers::core::abi::ethabi::EventParam {
                                    name: ::std::borrow::ToOwned::to_owned("previousOwner"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Address,
                                    indexed: true,
                                },
                                ::ethers::core::abi::ethabi::EventParam {
                                    name: ::std::borrow::ToOwned::to_owned("newOwner"),
                                    kind: ::ethers::core::abi::ethabi::ParamType::Address,
                                    indexed: true,
                                },
                            ],
                            anonymous: false,
                        },
                    ],
                ),
            ]),
            errors: ::std::collections::BTreeMap::new(),
            receive: false,
            fallback: false,
        }
    }
    ///The parsed JSON ABI of the contract.
    pub static SUMMA_ABI: ::ethers::contract::Lazy<::ethers::core::abi::Abi> = ::ethers::contract::Lazy::new(
        __abi,
    );
    #[rustfmt::skip]
    const __BYTECODE: &[u8] = b"`\xA04b\0\x01JW`\x1Fb\0\x1B\xF58\x81\x90\x03\x91\x82\x01`\x1F\x19\x16\x83\x01\x92`\x01`\x01`@\x1B\x03\x92\x90\x91\x83\x85\x11\x83\x86\x10\x17b\0\x01OW\x81`\x80\x92\x84\x92`@\x97\x88R\x839\x81\x01\x03\x12b\0\x01JW\x80Q`\x01`\x01`\xA0\x1B\x03\x90\x81\x81\x16\x81\x03b\0\x01JWb\0\0k` \x84\x01b\0\x01eV[\x91``b\0\0{\x87\x86\x01b\0\x01eV[\x94\x01Q\x94`\xFF\x86\x16\x92\x83\x87\x03b\0\x01JW`\0\x80T3`\x01`\x01`\xA0\x1B\x03\x19\x82\x16\x81\x17\x83U\x91\x94\x16\x7F\x8B\xE0\x07\x9CS\x16Y\x14\x13D\xCD\x1F\xD0\xA4\xF2\x84\x19I\x7F\x97\"\xA3\xDA\xAF\xE3\xB4\x18okdW\xE0\x85\x80\xA3`\x80R\x86Q\x91``\x83\x01\x91\x82\x11\x83\x83\x10\x17b\0\x016WPc\xFF\xFF\0\0\x93\x92\x91\x87\x91\x82Ra\xFF\xFF\x80\x94\x16\x93\x84\x82R\x86\x16` \x82\x01R\x01Rd\xFF\0\0\0\0`\x01T\x94` \x1B\x16\x93d\xFF\xFF\xFF\xFF\xFF\x19\x16\x17\x91`\x10\x1B\x16\x17\x17`\x01UQa\x1A\x7F\x90\x81b\0\x01v\x829`\x80Q\x81a\x18\x8B\x01R\xF3[cNH{q`\xE0\x1B\x81R`A`\x04R`$\x90\xFD[`\0\x80\xFD[cNH{q`\xE0\x1B`\0R`A`\x04R`$`\0\xFD[Q\x90a\xFF\xFF\x82\x16\x82\x03b\0\x01JWV\xFE`\x80\x80`@R`\x046\x10\x15a\0\x13W`\0\x80\xFD[`\x005`\xE0\x1C\x90\x81c\x19\xB39h\x14a\x12cWP\x80cI\xCE\x89\x97\x14a\x127W\x80cqP\x18\xA6\x14a\x11\xDEW\x80cyP,U\x14a\x11\xA5W\x80c\x8D\xA5\xCB[\x14a\x11|W\x80c\xA3\xC4\xBC\xF8\x14a\x10\xA8W\x80c\xC7\xDD\xCA\x0E\x14a\t\xB0W\x80c\xC8\xE5\x81G\x14a\tMW\x80c\xDAd\xA7P\x14a\x01]Wc\xF2\xFD\xE3\x8B\x14a\0\x8DW`\0\x80\xFD[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\x01`\x01`\xA0\x1B\x03\x81\x81\x16\x91\x82\x90\x03a\x01XWa\0\xBCa\x16uV[\x81\x15a\x01\x04W`\0T\x82k\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF`\xA0\x1B\x82\x16\x17`\0U\x16\x7F\x8B\xE0\x07\x9CS\x16Y\x14\x13D\xCD\x1F\xD0\xA4\xF2\x84\x19I\x7F\x97\"\xA3\xDA\xAF\xE3\xB4\x18okdW\xE0`\0\x80\xA3\0[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`&`$\x82\x01R\x7FOwnable: new owner is the zero a`D\x82\x01Reddress`\xD0\x1B`d\x82\x01R`\x84\x90\xFD[`\0\x80\xFD[4a\x01XW`\x806`\x03\x19\x01\x12a\x01XW`$5`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x01\x8D\x906\x90`\x04\x01a\x16\x17V[`\x01`\x01`@\x1B\x03`D5\x11a\x01XW6`#`D5\x01\x12\x15a\x01XW`D5`\x04\x015a\x01\xBA\x81a\x15\x9EV[a\x01\xC7`@Q\x91\x82a\x15}V[\x81\x81R` \x81\x01\x80\x926`$\x82`\x05\x1B`D5\x01\x01\x11a\x01XW`$`D5\x01\x91[`$\x82`\x05\x1B`D5\x01\x01\x83\x10a\x08\x9DWPPPa\x02\x05a\x16uV[a\x02\x12`\x045\x15\x15a\x17NV[\x82Q\x81Q\x03a\x08:Wa\x02%\x81Qa\x17\x8DV[\x90a\x020\x81Qa\x17\x8DV[\x93`\0[\x82Q\x81\x10\x15a\x03iW` a\x02I\x82\x85a\x16\xDCV[Q\x01QQ\x15\x15\x80a\x03TW[\x15a\x03\x16Wa\x02d\x81\x83a\x16\xDCV[Q\x15a\x02\xBFW\x80a\x02xa\x02\xBA\x92\x85a\x16\xDCV[QQa\x02\x84\x82\x87a\x16\xDCV[Ra\x02\x8F\x81\x86a\x16\xDCV[P` a\x02\x9C\x82\x86a\x16\xDCV[Q\x01Qa\x02\xA9\x82\x89a\x16\xDCV[Ra\x02\xB4\x81\x88a\x16\xDCV[Pa\x16\xCDV[a\x024V[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`)`$\x82\x01R\x7FAll root sums should be greater `D\x82\x01Rhthan zero`\xB8\x1B`d\x82\x01R`\x84\x90\xFD[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\x16`$\x82\x01RuInvalid cryptocurrency`P\x1B`D\x82\x01R`d\x90\xFD[Pa\x03_\x81\x84a\x16\xDCV[QQQ\x15\x15a\x02UV[P\x91\x84`@Q\x90a\x03y\x82a\x15bV[`\x045\x82R` \x82\x01\x92\x85\x84R`@\x83\x01R``\x82\x01R`d5`\0R`\x04` R`@`\0 \x91\x81Q\x83UQ\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!W`\x01`@\x1B\x82\x11a\x06!W` \x90`\x01\x85\x01T\x83`\x01\x87\x01U\x80\x84\x10a\x08\x1AW[P\x01`\x01\x84\x01`\0R` `\0 `\0[\x83\x81\x10a\x08\x06WPPPP`@\x81\x01Q\x80Q\x90`\x01`@\x1B\x82\x11a\x06!W`\x02\x84\x01T\x82`\x02\x86\x01U\x80\x83\x10a\x07\x8DW[P` \x01\x90`\x02\x84\x01`\0R` `\0 \x91`\0\x90[\x82\x82\x10a\x06\xB0WPPPP``\x01Q\x80Q\x90`\x01`@\x1B\x82\x11a\x06!W`\x03\x83\x01T\x82`\x03\x85\x01U\x80\x83\x10a\x067W[P` `\x03\x91\x01\x92\x01`\0R` `\0 \x91`\0\x90[\x82\x82\x10a\x05>WPPPPa\x04\x9E`@Q\x92`\x045\x84R``` \x85\x01R``\x84\x01\x90a\x17\xD7V[\x90\x82\x82\x03`@\x84\x01RQ\x80\x82R` \x82\x01\x91` \x82`\x05\x1B\x82\x01\x01\x94\x92`\0\x91[\x83\x83\x10a\x04\xF1W`d5\x7F\x88\xBF\xC78\x9C\xB81\xEA\x02\x08\xFF\x10m\xA6\xF5\xC9\xF8\x806\xBA\x08O\x1E\xB0\x08\xD2x\x8D=E\x99\x8D\x87\x89\x03\x88\xA2\0[\x90\x91\x92\x93\x95` \x80a\x05/`\x01\x93`\x1F\x19\x86\x82\x03\x01\x87R\x8AQ\x90\x83a\x05\x1F\x83Q`@\x84R`@\x84\x01\x90a\x13\xC6V[\x92\x01Q\x90\x84\x81\x84\x03\x91\x01Ra\x13\xC6V[\x98\x01\x93\x01\x93\x01\x91\x93\x92\x90a\x04\xBFV[\x80Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x05e\x82a\x05_\x88Ta\x14\x92V[\x88a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\x05\xB1W\x92\x82`\x01\x94\x93` \x93\x86\x95`\0\x92a\x05\xA6W[PP`\0\x19`\x03\x83\x90\x1B\x1C\x19\x16\x90\x84\x1B\x17\x87U[\x01\x94\x01\x91\x01\x90\x92a\x04vV[\x01Q\x90P\x8C\x80a\x05\x86V[\x90\x86`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\x06\tWP\x83` \x93`\x01\x96\x93\x87\x96\x93\x87\x94`\x1F\x19\x81\x16\x10a\x05\xF0W[PPP\x81\x1B\x01\x87Ua\x05\x9AV[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x8C\x80\x80a\x05\xE3V[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\x05\xBFV[cNH{q`\xE0\x1B`\0R`A`\x04R`$`\0\xFD[`\x03\x84\x01`\0R` `\0 \x90\x83\x82\x01[\x81\x83\x01\x81\x10a\x06XWPPa\x04`V[\x80a\x06e`\x01\x92Ta\x14\x92V[\x80a\x06rW[P\x01a\x06HV[`\x1F\x90\x81\x81\x11\x84\x14a\x06\x8BWPP`\0\x81U[\x8Aa\x06kV[a\x06\xA7`\0\x92\x84\x84R` \x84 \x92\x01`\x05\x1C\x82\x01\x85\x83\x01a\x16\xF0V[\x81\x83UUa\x06\x85V[\x80Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x06\xD1\x82a\x05_\x88Ta\x14\x92V[` \x90`\x1F\x83\x11`\x01\x14a\x07\x1DW\x92\x82`\x01\x94\x93` \x93\x86\x95`\0\x92a\x07\x12W[PP`\0\x19`\x03\x83\x90\x1B\x1C\x19\x16\x90\x84\x1B\x17\x87U[\x01\x94\x01\x91\x01\x90\x92a\x040V[\x01Q\x90P\x8E\x80a\x06\xF2V[\x90\x86`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\x07uWP\x83` \x93`\x01\x96\x93\x87\x96\x93\x87\x94`\x1F\x19\x81\x16\x10a\x07\\W[PPP\x81\x1B\x01\x87Ua\x07\x06V[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x8E\x80\x80a\x07OV[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\x07+V[`\x02\x85\x01`\0R` `\0 \x90\x83\x82\x01[\x81\x83\x01\x81\x10a\x07\xAEWPPa\x04\x1AV[\x80a\x07\xBB`\x01\x92Ta\x14\x92V[\x80a\x07\xC8W[P\x01a\x07\x9EV[`\x1F\x90\x81\x81\x11\x84\x14a\x07\xE1WPP`\0\x81U[\x8Ba\x07\xC1V[a\x07\xFD`\0\x92\x84\x84R` \x84 \x92\x01`\x05\x1C\x82\x01\x85\x83\x01a\x16\xF0V[\x81\x83UUa\x07\xDBV[`\x01\x90` \x84Q\x94\x01\x93\x81\x84\x01U\x01a\x03\xE9V[a\x084\x90`\x01\x87\x01`\0R\x84\x84`\0 \x91\x82\x01\x91\x01a\x16\xF0V[\x88a\x03\xD8V[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`5`$\x82\x01R\x7FRoot liabilities sums and liabil`D\x82\x01Rt\r.\x8D,\xAEd\r\xCE\xAD\xACL\xAED\r\xAD.m\xAC.\x8Cm`[\x1B`d\x82\x01R`\x84\x90\xFD[\x825\x90`\x01`\x01`@\x1B\x03\x82\x11a\x01XW`@`D5\x83\x016\x03`#\x19\x01\x12a\x01XW`@Q\x91`@\x83\x01\x83\x81\x10`\x01`\x01`@\x1B\x03\x82\x11\x17a\x06!W`@R`\x01`\x01`@\x1B\x03`$\x82`D5\x01\x015\x11a\x01XWa\t\t6`$`D5\x84\x01\x81\x81\x015\x01\x01a\x15\xD0V[\x83R`D\x81\x815\x01\x015\x91`\x01`\x01`@\x1B\x03\x83\x11a\x01XW`$\x93a\t<` \x94\x93\x86\x86\x956\x92`D5\x01\x01\x01a\x15\xD0V[\x83\x82\x01R\x81R\x01\x93\x01\x92\x90Pa\x01\xE9V[4a\x01XW``6`\x03\x19\x01\x12a\x01XW`\x01`\x01`@\x1B\x03`\x045\x81\x81\x11a\x01XWa\t~\x906\x90`\x04\x01a\x15\xD0V[\x90`$5\x90\x81\x11a\x01XW` \x91a\t\x9Da\t\xA6\x926\x90`\x04\x01a\x16\x17V[`D5\x91a\x18\x0BV[`@Q\x90\x15\x15\x81R\xF3[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\x01`\x01`@\x1B\x03\x81\x11a\x01XW6`#\x82\x01\x12\x15a\x01XW\x80`\x04\x015\x90a\t\xEC\x82a\x15\x9EV[\x90a\t\xFA`@Q\x92\x83a\x15}V[\x82\x82R` \x82\x01\x90`$\x82\x94`\x05\x1B\x82\x01\x01\x906\x82\x11a\x01XW`$\x81\x01\x92[\x82\x84\x10a\x0F\xCEW\x85\x85a\n+a\x16uV[`\0[\x81Q\x81\x10\x15a\x0FNWa\nA\x81\x83a\x16\xDCV[QQ`@Qa\nm` \x82\x81a\n`\x81\x83\x01\x96\x87\x81Q\x93\x84\x92\x01a\x13\xA3V[\x81\x01\x03\x80\x84R\x01\x82a\x15}V[Q\x90 \x80`\0R`\x03` R`@`\0 Ta\x0F\tWa\n\x8D\x82\x84a\x16\xDCV[Q`\x02T`\x01`@\x1B\x81\x10\x15a\x06!W\x80`\x01a\n\xAD\x92\x01`\x02Ua\x14BV[\x91\x90\x91a\x0E\xF3W\x80Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!W\x81\x90a\n\xDD\x82a\n\xD7\x87Ta\x14\x92V[\x87a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\x0E\x87W`\0\x92a\x0E|W[PP\x81`\x01\x1B\x91`\0\x19\x90`\x03\x1B\x1C\x19\x16\x17\x82U[` \x81\x01Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!W\x81\x90a\x0B:\x82a\x0B1`\x01\x88\x01Ta\x14\x92V[`\x01\x88\x01a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\x0E\nW`\0\x92a\r\xFFW[PP\x81`\x01\x1B\x91`\0\x19\x90`\x03\x1B\x1C\x19\x16\x17`\x01\x83\x01U[`@\x81\x01Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x0B\x98\x82a\x0B\x8F`\x02\x87\x01Ta\x14\x92V[`\x02\x87\x01a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\r\x8CW``\x93\x92\x91`\0\x91\x83a\r\x81W[PP\x81`\x01\x1B\x91`\0\x19\x90`\x03\x1B\x1C\x19\x16\x17`\x02\x84\x01U[\x01Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x0B\xF9\x82a\x0B\xF0`\x03\x86\x01Ta\x14\x92V[`\x03\x86\x01a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\r\x12W`\x03\x92\x91`\0\x91\x83a\r\x07W[PP\x81`\x01\x1B\x91`\0\x19\x90\x84\x1B\x1C\x19\x16\x17\x91\x01U[`\x02T\x90`\0R`\x03` R`@`\0 Ua\x0CE\x81\x83a\x16\xDCV[QQQ\x15\x15\x80a\x0C\xEFW[\x80a\x0C\xD7W[\x80a\x0C\xBFW[\x15a\x0CoWa\x0Cj\x90a\x16\xCDV[a\n.V[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\"`$\x82\x01R\x7FInvalid proof of address ownersh`D\x82\x01Ra\x06\x97`\xF4\x1B`d\x82\x01R`\x84\x90\xFD[P``a\x0C\xCC\x82\x84a\x16\xDCV[Q\x01QQ\x15\x15a\x0C\\V[P`@a\x0C\xE4\x82\x84a\x16\xDCV[Q\x01QQ\x15\x15a\x0CVV[P` a\x0C\xFC\x82\x84a\x16\xDCV[Q\x01QQ\x15\x15a\x0CPV[\x01Q\x90P\x88\x80a\x0C\x14V[\x90`\x03\x84\x01`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\riWP\x91\x83\x91`\x01\x93`\x03\x95`\x1F\x19\x81\x16\x10a\rQW[PPP\x81\x1B\x01\x91\x01Ua\x0C)V[\x01Q`\0\x19\x83\x86\x1B`\xF8\x16\x1C\x19\x16\x90U\x88\x80\x80a\rCV[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\r#V[\x01Q\x90P\x89\x80a\x0B\xB4V[\x90`\x02\x85\x01`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\r\xE7WP\x91\x83\x91`\x01\x93``\x96\x95`\x1F\x19\x81\x16\x10a\r\xCEW[PPP\x81\x1B\x01`\x02\x84\x01Ua\x0B\xCCV[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x89\x80\x80a\r\xBEV[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\r\x9DV[\x01Q\x90P\x88\x80a\x0BPV[\x92P`\x01\x85\x01`\0R` `\0 \x90`\0\x93[`\x1F\x19\x84\x16\x85\x10a\x0EaW`\x01\x94P\x83`\x1F\x19\x81\x16\x10a\x0EHW[PPP\x81\x1B\x01`\x01\x83\x01Ua\x0BhV[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x88\x80\x80a\x0E8V[\x81\x81\x01Q\x83U` \x94\x85\x01\x94`\x01\x90\x93\x01\x92\x90\x91\x01\x90a\x0E\x1DV[\x01Q\x90P\x88\x80a\n\xF3V[\x92P\x84`\0R` `\0 \x90`\0\x93[`\x1F\x19\x84\x16\x85\x10a\x0E\xD8W`\x01\x94P\x83`\x1F\x19\x81\x16\x10a\x0E\xBFW[PPP\x81\x1B\x01\x82Ua\x0B\x08V[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x88\x80\x80a\x0E\xB2V[\x81\x81\x01Q\x83U` \x94\x85\x01\x94`\x01\x90\x93\x01\x92\x90\x91\x01\x90a\x0E\x97V[cNH{q`\xE0\x1B`\0R`\0`\x04R`$`\0\xFD[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\x18`$\x82\x01R\x7FAddress already verified\0\0\0\0\0\0\0\0`D\x82\x01R`d\x90\xFD[P`@Q\x90` \x82\x01\x90` \x83RQ\x80\x91R`@\x82\x01\x90`@\x81`\x05\x1B\x84\x01\x01\x93\x91`\0\x90[\x82\x82\x10a\x0F\xA3W\x7F8#\x15\xD4\xD5j`5\xE1\x89\x9B\xFF\xE7}\x9B\xEC\xEF\xAF_&P\xE42;'\x85HW\xA0EFX\x85\x87\x03\x86\xA1\0[\x90\x91\x92\x94` \x80a\x0F\xC0`\x01\x93`?\x19\x89\x82\x03\x01\x86R\x89Qa\x13\xEBV[\x97\x01\x92\x01\x92\x01\x90\x92\x91a\x0FtV[\x835`\x01`\x01`@\x1B\x03\x81\x11a\x01XW\x82\x01`\x80`#\x19\x826\x03\x01\x12a\x01XW`@Q\x91a\x0F\xFB\x83a\x15bV[`$\x82\x015`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x10\x1E\x90`$6\x91\x85\x01\x01a\x15\xD0V[\x83R`D\x82\x015`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x10C\x90`$6\x91\x85\x01\x01a\x15\xD0V[` \x84\x01R`d\x82\x015`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x10k\x90`$6\x91\x85\x01\x01a\x15\xD0V[`@\x84\x01R`\x84\x82\x015\x92`\x01`\x01`@\x1B\x03\x84\x11a\x01XWa\x10\x98` \x94\x93`$\x86\x956\x92\x01\x01a\x15\xD0V[``\x82\x01R\x81R\x01\x93\x01\x92a\n\x1AV[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\x02T\x81\x10\x15a\x01XWa\x10\xD2a\x11N\x91a\x14BV[Pa\x11x`\x03a\x11j`@Q\x93a\x10\xF4\x85a\x10\xED\x81\x84a\x14\xCCV[\x03\x86a\x15}V[a\x11\\`@Qa\x11\x12\x81a\x11\x0B\x81`\x01\x87\x01a\x14\xCCV[\x03\x82a\x15}V[a\x11:`@Q\x93a\x11*\x85a\x10\xED\x81`\x02\x85\x01a\x14\xCCV[a\x10\xED`@Q\x80\x98\x81\x93\x01a\x14\xCCV[`@Q\x97\x88\x97`\x80\x89R`\x80\x89\x01\x90a\x13\xC6V[\x90\x87\x82\x03` \x89\x01Ra\x13\xC6V[\x90\x85\x82\x03`@\x87\x01Ra\x13\xC6V[\x90\x83\x82\x03``\x85\x01Ra\x13\xC6V[\x03\x90\xF3[4a\x01XW`\x006`\x03\x19\x01\x12a\x01XW`\0T`@Q`\x01`\x01`\xA0\x1B\x03\x90\x91\x16\x81R` \x90\xF3[4a\x01XW`\x006`\x03\x19\x01\x12a\x01XW```\x01T`\xFF`@Q\x91a\xFF\xFF\x80\x82\x16\x84R\x81`\x10\x1C\x16` \x84\x01R` \x1C\x16`@\x82\x01R\xF3[4a\x01XW`\x006`\x03\x19\x01\x12a\x01XWa\x11\xF7a\x16uV[`\0\x80T`\x01`\x01`\xA0\x1B\x03\x19\x81\x16\x82U`\x01`\x01`\xA0\x1B\x03\x16\x7F\x8B\xE0\x07\x9CS\x16Y\x14\x13D\xCD\x1F\xD0\xA4\xF2\x84\x19I\x7F\x97\"\xA3\xDA\xAF\xE3\xB4\x18okdW\xE0\x82\x80\xA3\0[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\0R`\x04` R` `@`\0 T`@Q\x90\x81R\xF3[4a\x01XW` \x80`\x03\x196\x01\x12a\x01XW`\x045a\x12\x81\x83a\x15bV[``\x80\x84\x81\x80\x96R\x81\x85\x82\x01R\x81`@\x82\x01R\x01R\x80`\0R`\x03\x82R`@`\0 T\x15a\x13gW`\0R`\x03\x81R`@`\0 T`\0\x19\x81\x01\x90\x81\x11a\x13QWa\x12\xCD`\x03\x91a\x14BV[P\x92a\x13:`@Q\x94a\x12\xDF\x86a\x15bV[`@Qa\x12\xF0\x81a\x11\x0B\x81\x85a\x14\xCCV[\x86R`@Qa\x13\x06\x81a\x11\x0B\x81`\x01\x86\x01a\x14\xCCV[\x85\x87\x01R`@Qa\x13\x1E\x81a\x11\x0B\x81`\x02\x86\x01a\x14\xCCV[`@\x87\x01Ra\x133`@Q\x80\x95\x81\x93\x01a\x14\xCCV[\x03\x83a\x15}V[\x83\x01Ra\x11x`@Q\x92\x82\x84\x93\x84R\x83\x01\x90a\x13\xEBV[cNH{q`\xE0\x1B`\0R`\x11`\x04R`$`\0\xFD[`@QbF\x1B\xCD`\xE5\x1B\x81R`\x04\x81\x01\x83\x90R`\x14`$\x82\x01Rs\x10Y\x19\x1C\x99\\\xDC\xC8\x1B\x9B\xDD\x08\x1D\x99\\\x9AY\x9AYY`b\x1B`D\x82\x01R`d\x90\xFD[`\0[\x83\x81\x10a\x13\xB6WPP`\0\x91\x01RV[\x81\x81\x01Q\x83\x82\x01R` \x01a\x13\xA6V[\x90` \x91a\x13\xDF\x81Q\x80\x92\x81\x85R\x85\x80\x86\x01\x91\x01a\x13\xA3V[`\x1F\x01`\x1F\x19\x16\x01\x01\x90V[a\x14?\x91``a\x14.a\x14\x1Ca\x14\n\x85Q`\x80\x86R`\x80\x86\x01\x90a\x13\xC6V[` \x86\x01Q\x85\x82\x03` \x87\x01Ra\x13\xC6V[`@\x85\x01Q\x84\x82\x03`@\x86\x01Ra\x13\xC6V[\x92\x01Q\x90``\x81\x84\x03\x91\x01Ra\x13\xC6V[\x90V[`\x02T\x81\x10\x15a\x14|W`\x02`\0R`\x02\x1B\x7F@W\x87\xFA\x12\xA8#\xE0\xF2\xB7c\x1C\xC4\x1B;\xA8\x82\x8B3!\xCA\x81\x11\x11\xFAu\xCD:\xA3\xBBZ\xCE\x01\x90`\0\x90V[cNH{q`\xE0\x1B`\0R`2`\x04R`$`\0\xFD[\x90`\x01\x82\x81\x1C\x92\x16\x80\x15a\x14\xC2W[` \x83\x10\x14a\x14\xACWV[cNH{q`\xE0\x1B`\0R`\"`\x04R`$`\0\xFD[\x91`\x7F\x16\x91a\x14\xA1V[\x90`\0\x92\x91\x80T\x91a\x14\xDD\x83a\x14\x92V[\x91\x82\x82R`\x01\x93\x84\x81\x16\x90\x81`\0\x14a\x15?WP`\x01\x14a\x14\xFFW[PPPPV[\x90\x91\x93\x94P`\0R` \x92\x83`\0 \x92\x84`\0\x94[\x83\x86\x10a\x15+WPPPP\x01\x01\x908\x80\x80\x80a\x14\xF9V[\x80T\x85\x87\x01\x83\x01R\x94\x01\x93\x85\x90\x82\x01a\x15\x14V[\x92\x94PPP` \x93\x94P`\xFF\x19\x16\x83\x83\x01R\x15\x15`\x05\x1B\x01\x01\x908\x80\x80\x80a\x14\xF9V[`\x80\x81\x01\x90\x81\x10`\x01`\x01`@\x1B\x03\x82\x11\x17a\x06!W`@RV[\x90`\x1F\x80\x19\x91\x01\x16\x81\x01\x90\x81\x10`\x01`\x01`@\x1B\x03\x82\x11\x17a\x06!W`@RV[`\x01`\x01`@\x1B\x03\x81\x11a\x06!W`\x05\x1B` \x01\x90V[`\x01`\x01`@\x1B\x03\x81\x11a\x06!W`\x1F\x01`\x1F\x19\x16` \x01\x90V[\x81`\x1F\x82\x01\x12\x15a\x01XW\x805\x90a\x15\xE7\x82a\x15\xB5V[\x92a\x15\xF5`@Q\x94\x85a\x15}V[\x82\x84R` \x83\x83\x01\x01\x11a\x01XW\x81`\0\x92` \x80\x93\x01\x83\x86\x017\x83\x01\x01R\x90V[\x81`\x1F\x82\x01\x12\x15a\x01XW\x805\x91a\x16.\x83a\x15\x9EV[\x92a\x16<`@Q\x94\x85a\x15}V[\x80\x84R` \x92\x83\x80\x86\x01\x92`\x05\x1B\x82\x01\x01\x92\x83\x11a\x01XW\x83\x01\x90[\x82\x82\x10a\x16fWPPPP\x90V[\x815\x81R\x90\x83\x01\x90\x83\x01a\x16XV[`\0T`\x01`\x01`\xA0\x1B\x03\x163\x03a\x16\x89WV[`d`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R` `$\x82\x01R\x7FOwnable: caller is not the owner`D\x82\x01R\xFD[`\0\x19\x81\x14a\x13QW`\x01\x01\x90V[\x80Q\x82\x10\x15a\x14|W` \x91`\x05\x1B\x01\x01\x90V[\x81\x81\x10a\x16\xFBWPPV[`\0\x81U`\x01\x01a\x16\xF0V[\x91\x90`\x1F\x81\x11a\x17\x16WPPPV[a\x17B\x92`\0R` `\0 \x90` `\x1F\x84\x01`\x05\x1C\x83\x01\x93\x10a\x17DW[`\x1F\x01`\x05\x1C\x01\x90a\x16\xF0V[V[\x90\x91P\x81\x90a\x175V[\x15a\x17UWV[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\x10`$\x82\x01Ro\x12[\x9D\x98[\x1AY\x08\x13T\xD5\x08\x1C\x9B\xDB\xDD`\x82\x1B`D\x82\x01R`d\x90\xFD[\x90a\x17\x97\x82a\x15\x9EV[a\x17\xA4`@Q\x91\x82a\x15}V[\x82\x81R\x80\x92a\x17\xB5`\x1F\x19\x91a\x15\x9EV[\x01\x90`\0[\x82\x81\x10a\x17\xC6WPPPV[\x80``` \x80\x93\x85\x01\x01R\x01a\x17\xBAV[\x90\x81Q\x80\x82R` \x80\x80\x93\x01\x93\x01\x91`\0[\x82\x81\x10a\x17\xF7WPPPP\x90V[\x83Q\x85R\x93\x81\x01\x93\x92\x81\x01\x92`\x01\x01a\x17\xE9V[\x90\x91`\0\x81\x81R`\x04\x93` \x93\x85\x85R`@\x93\x84\x84 T\x90\x83Q\x91`\x01\x92\x83\x10\x15a\x1A6W\x90a\x18B\x88\x94\x93\x92\x88\x87\x01Q\x14a\x17NV[`\x02\x82[a\x19tW[PPPa\x18u\x90a\x18\x87\x86Q\x94\x85\x93\x84\x93c\x1E\x8E\x1E\x13`\xE0\x1B\x85R\x89\x8C\x86\x01R`D\x85\x01\x90a\x13\xC6V[\x83\x81\x03`\x03\x19\x01`$\x85\x01R\x90a\x17\xD7V[\x03\x81\x7F\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0`\x01`\x01`\xA0\x1B\x03\x16Z\xFA\x82\x91\x81a\x198W[Pa\x190WP`d\x94P=\x15a\x19*W=\x90a\x18\xD8\x82a\x15\xB5V[\x91a\x18\xE5\x84Q\x93\x84a\x15}V[\x82R\x83=\x92\x01>[QbF\x1B\xCD`\xE5\x1B\x81R\x91\x82\x01R`\x17`$\x82\x01R\x7FInvalid inclusion proof\0\0\0\0\0\0\0\0\0`D\x82\x01R\xFD[Pa\x18\xEDV[\x93PPPP\x90V[\x90\x91P\x84\x81\x81=\x83\x11a\x19mW[a\x19P\x81\x83a\x15}V[\x81\x01\x03\x12a\x19iWQ\x80\x15\x15\x81\x03a\x19iW\x908a\x18\xBDV[\x82\x80\xFD[P=a\x19FV[\x90\x91\x92\x93\x85Q\x82\x10\x15a\x1A/WP\x81\x86R\x88\x88R\x86\x86 `\x01\x19\x90\x84\x01\x82\x82\x01\x83\x81\x11a\x1A\x1CW\x81T\x11\x15a\x1A\tW\x87R\x81\x89\x88 \x01\x01Ta\x19\xB6\x82\x87a\x16\xDCV[Q\x03a\x19\xCFW\x90a\x19\xC7\x83\x92a\x16\xCDV[\x88\x94\x93a\x18FV[\x86QbF\x1B\xCD`\xE5\x1B\x81R\x80\x8A\x01\x89\x90R`\x14`$\x82\x01RsInvalid root balance``\x1B`D\x82\x01R`d\x90\xFD[cNH{q`\xE0\x1B\x88R`2\x8BR`$\x88\xFD[cNH{q`\xE0\x1B\x89R`\x11\x8CR`$\x89\xFD[\x93\x92a\x18KV[cNH{q`\xE0\x1B\x86R`2\x89R`$\x86\xFD\xFE\xA2dipfsX\"\x12 Liu\0\x97k\x80\xEB\xFD\xB9L\x86\x19q0\xF8[Bw\xC7Ib\x08\xD4\x02\xA9\xE6'\x92PS\xF2dsolcC\0\x08\x12\x003";
    /// The bytecode of the contract.
    pub static SUMMA_BYTECODE: ::ethers::core::types::Bytes = ::ethers::core::types::Bytes::from_static(
        __BYTECODE,
    );
    #[rustfmt::skip]
    const __DEPLOYED_BYTECODE: &[u8] = b"`\x80\x80`@R`\x046\x10\x15a\0\x13W`\0\x80\xFD[`\x005`\xE0\x1C\x90\x81c\x19\xB39h\x14a\x12cWP\x80cI\xCE\x89\x97\x14a\x127W\x80cqP\x18\xA6\x14a\x11\xDEW\x80cyP,U\x14a\x11\xA5W\x80c\x8D\xA5\xCB[\x14a\x11|W\x80c\xA3\xC4\xBC\xF8\x14a\x10\xA8W\x80c\xC7\xDD\xCA\x0E\x14a\t\xB0W\x80c\xC8\xE5\x81G\x14a\tMW\x80c\xDAd\xA7P\x14a\x01]Wc\xF2\xFD\xE3\x8B\x14a\0\x8DW`\0\x80\xFD[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\x01`\x01`\xA0\x1B\x03\x81\x81\x16\x91\x82\x90\x03a\x01XWa\0\xBCa\x16uV[\x81\x15a\x01\x04W`\0T\x82k\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF\xFF`\xA0\x1B\x82\x16\x17`\0U\x16\x7F\x8B\xE0\x07\x9CS\x16Y\x14\x13D\xCD\x1F\xD0\xA4\xF2\x84\x19I\x7F\x97\"\xA3\xDA\xAF\xE3\xB4\x18okdW\xE0`\0\x80\xA3\0[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`&`$\x82\x01R\x7FOwnable: new owner is the zero a`D\x82\x01Reddress`\xD0\x1B`d\x82\x01R`\x84\x90\xFD[`\0\x80\xFD[4a\x01XW`\x806`\x03\x19\x01\x12a\x01XW`$5`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x01\x8D\x906\x90`\x04\x01a\x16\x17V[`\x01`\x01`@\x1B\x03`D5\x11a\x01XW6`#`D5\x01\x12\x15a\x01XW`D5`\x04\x015a\x01\xBA\x81a\x15\x9EV[a\x01\xC7`@Q\x91\x82a\x15}V[\x81\x81R` \x81\x01\x80\x926`$\x82`\x05\x1B`D5\x01\x01\x11a\x01XW`$`D5\x01\x91[`$\x82`\x05\x1B`D5\x01\x01\x83\x10a\x08\x9DWPPPa\x02\x05a\x16uV[a\x02\x12`\x045\x15\x15a\x17NV[\x82Q\x81Q\x03a\x08:Wa\x02%\x81Qa\x17\x8DV[\x90a\x020\x81Qa\x17\x8DV[\x93`\0[\x82Q\x81\x10\x15a\x03iW` a\x02I\x82\x85a\x16\xDCV[Q\x01QQ\x15\x15\x80a\x03TW[\x15a\x03\x16Wa\x02d\x81\x83a\x16\xDCV[Q\x15a\x02\xBFW\x80a\x02xa\x02\xBA\x92\x85a\x16\xDCV[QQa\x02\x84\x82\x87a\x16\xDCV[Ra\x02\x8F\x81\x86a\x16\xDCV[P` a\x02\x9C\x82\x86a\x16\xDCV[Q\x01Qa\x02\xA9\x82\x89a\x16\xDCV[Ra\x02\xB4\x81\x88a\x16\xDCV[Pa\x16\xCDV[a\x024V[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`)`$\x82\x01R\x7FAll root sums should be greater `D\x82\x01Rhthan zero`\xB8\x1B`d\x82\x01R`\x84\x90\xFD[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\x16`$\x82\x01RuInvalid cryptocurrency`P\x1B`D\x82\x01R`d\x90\xFD[Pa\x03_\x81\x84a\x16\xDCV[QQQ\x15\x15a\x02UV[P\x91\x84`@Q\x90a\x03y\x82a\x15bV[`\x045\x82R` \x82\x01\x92\x85\x84R`@\x83\x01R``\x82\x01R`d5`\0R`\x04` R`@`\0 \x91\x81Q\x83UQ\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!W`\x01`@\x1B\x82\x11a\x06!W` \x90`\x01\x85\x01T\x83`\x01\x87\x01U\x80\x84\x10a\x08\x1AW[P\x01`\x01\x84\x01`\0R` `\0 `\0[\x83\x81\x10a\x08\x06WPPPP`@\x81\x01Q\x80Q\x90`\x01`@\x1B\x82\x11a\x06!W`\x02\x84\x01T\x82`\x02\x86\x01U\x80\x83\x10a\x07\x8DW[P` \x01\x90`\x02\x84\x01`\0R` `\0 \x91`\0\x90[\x82\x82\x10a\x06\xB0WPPPP``\x01Q\x80Q\x90`\x01`@\x1B\x82\x11a\x06!W`\x03\x83\x01T\x82`\x03\x85\x01U\x80\x83\x10a\x067W[P` `\x03\x91\x01\x92\x01`\0R` `\0 \x91`\0\x90[\x82\x82\x10a\x05>WPPPPa\x04\x9E`@Q\x92`\x045\x84R``` \x85\x01R``\x84\x01\x90a\x17\xD7V[\x90\x82\x82\x03`@\x84\x01RQ\x80\x82R` \x82\x01\x91` \x82`\x05\x1B\x82\x01\x01\x94\x92`\0\x91[\x83\x83\x10a\x04\xF1W`d5\x7F\x88\xBF\xC78\x9C\xB81\xEA\x02\x08\xFF\x10m\xA6\xF5\xC9\xF8\x806\xBA\x08O\x1E\xB0\x08\xD2x\x8D=E\x99\x8D\x87\x89\x03\x88\xA2\0[\x90\x91\x92\x93\x95` \x80a\x05/`\x01\x93`\x1F\x19\x86\x82\x03\x01\x87R\x8AQ\x90\x83a\x05\x1F\x83Q`@\x84R`@\x84\x01\x90a\x13\xC6V[\x92\x01Q\x90\x84\x81\x84\x03\x91\x01Ra\x13\xC6V[\x98\x01\x93\x01\x93\x01\x91\x93\x92\x90a\x04\xBFV[\x80Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x05e\x82a\x05_\x88Ta\x14\x92V[\x88a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\x05\xB1W\x92\x82`\x01\x94\x93` \x93\x86\x95`\0\x92a\x05\xA6W[PP`\0\x19`\x03\x83\x90\x1B\x1C\x19\x16\x90\x84\x1B\x17\x87U[\x01\x94\x01\x91\x01\x90\x92a\x04vV[\x01Q\x90P\x8C\x80a\x05\x86V[\x90\x86`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\x06\tWP\x83` \x93`\x01\x96\x93\x87\x96\x93\x87\x94`\x1F\x19\x81\x16\x10a\x05\xF0W[PPP\x81\x1B\x01\x87Ua\x05\x9AV[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x8C\x80\x80a\x05\xE3V[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\x05\xBFV[cNH{q`\xE0\x1B`\0R`A`\x04R`$`\0\xFD[`\x03\x84\x01`\0R` `\0 \x90\x83\x82\x01[\x81\x83\x01\x81\x10a\x06XWPPa\x04`V[\x80a\x06e`\x01\x92Ta\x14\x92V[\x80a\x06rW[P\x01a\x06HV[`\x1F\x90\x81\x81\x11\x84\x14a\x06\x8BWPP`\0\x81U[\x8Aa\x06kV[a\x06\xA7`\0\x92\x84\x84R` \x84 \x92\x01`\x05\x1C\x82\x01\x85\x83\x01a\x16\xF0V[\x81\x83UUa\x06\x85V[\x80Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x06\xD1\x82a\x05_\x88Ta\x14\x92V[` \x90`\x1F\x83\x11`\x01\x14a\x07\x1DW\x92\x82`\x01\x94\x93` \x93\x86\x95`\0\x92a\x07\x12W[PP`\0\x19`\x03\x83\x90\x1B\x1C\x19\x16\x90\x84\x1B\x17\x87U[\x01\x94\x01\x91\x01\x90\x92a\x040V[\x01Q\x90P\x8E\x80a\x06\xF2V[\x90\x86`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\x07uWP\x83` \x93`\x01\x96\x93\x87\x96\x93\x87\x94`\x1F\x19\x81\x16\x10a\x07\\W[PPP\x81\x1B\x01\x87Ua\x07\x06V[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x8E\x80\x80a\x07OV[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\x07+V[`\x02\x85\x01`\0R` `\0 \x90\x83\x82\x01[\x81\x83\x01\x81\x10a\x07\xAEWPPa\x04\x1AV[\x80a\x07\xBB`\x01\x92Ta\x14\x92V[\x80a\x07\xC8W[P\x01a\x07\x9EV[`\x1F\x90\x81\x81\x11\x84\x14a\x07\xE1WPP`\0\x81U[\x8Ba\x07\xC1V[a\x07\xFD`\0\x92\x84\x84R` \x84 \x92\x01`\x05\x1C\x82\x01\x85\x83\x01a\x16\xF0V[\x81\x83UUa\x07\xDBV[`\x01\x90` \x84Q\x94\x01\x93\x81\x84\x01U\x01a\x03\xE9V[a\x084\x90`\x01\x87\x01`\0R\x84\x84`\0 \x91\x82\x01\x91\x01a\x16\xF0V[\x88a\x03\xD8V[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`5`$\x82\x01R\x7FRoot liabilities sums and liabil`D\x82\x01Rt\r.\x8D,\xAEd\r\xCE\xAD\xACL\xAED\r\xAD.m\xAC.\x8Cm`[\x1B`d\x82\x01R`\x84\x90\xFD[\x825\x90`\x01`\x01`@\x1B\x03\x82\x11a\x01XW`@`D5\x83\x016\x03`#\x19\x01\x12a\x01XW`@Q\x91`@\x83\x01\x83\x81\x10`\x01`\x01`@\x1B\x03\x82\x11\x17a\x06!W`@R`\x01`\x01`@\x1B\x03`$\x82`D5\x01\x015\x11a\x01XWa\t\t6`$`D5\x84\x01\x81\x81\x015\x01\x01a\x15\xD0V[\x83R`D\x81\x815\x01\x015\x91`\x01`\x01`@\x1B\x03\x83\x11a\x01XW`$\x93a\t<` \x94\x93\x86\x86\x956\x92`D5\x01\x01\x01a\x15\xD0V[\x83\x82\x01R\x81R\x01\x93\x01\x92\x90Pa\x01\xE9V[4a\x01XW``6`\x03\x19\x01\x12a\x01XW`\x01`\x01`@\x1B\x03`\x045\x81\x81\x11a\x01XWa\t~\x906\x90`\x04\x01a\x15\xD0V[\x90`$5\x90\x81\x11a\x01XW` \x91a\t\x9Da\t\xA6\x926\x90`\x04\x01a\x16\x17V[`D5\x91a\x18\x0BV[`@Q\x90\x15\x15\x81R\xF3[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\x01`\x01`@\x1B\x03\x81\x11a\x01XW6`#\x82\x01\x12\x15a\x01XW\x80`\x04\x015\x90a\t\xEC\x82a\x15\x9EV[\x90a\t\xFA`@Q\x92\x83a\x15}V[\x82\x82R` \x82\x01\x90`$\x82\x94`\x05\x1B\x82\x01\x01\x906\x82\x11a\x01XW`$\x81\x01\x92[\x82\x84\x10a\x0F\xCEW\x85\x85a\n+a\x16uV[`\0[\x81Q\x81\x10\x15a\x0FNWa\nA\x81\x83a\x16\xDCV[QQ`@Qa\nm` \x82\x81a\n`\x81\x83\x01\x96\x87\x81Q\x93\x84\x92\x01a\x13\xA3V[\x81\x01\x03\x80\x84R\x01\x82a\x15}V[Q\x90 \x80`\0R`\x03` R`@`\0 Ta\x0F\tWa\n\x8D\x82\x84a\x16\xDCV[Q`\x02T`\x01`@\x1B\x81\x10\x15a\x06!W\x80`\x01a\n\xAD\x92\x01`\x02Ua\x14BV[\x91\x90\x91a\x0E\xF3W\x80Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!W\x81\x90a\n\xDD\x82a\n\xD7\x87Ta\x14\x92V[\x87a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\x0E\x87W`\0\x92a\x0E|W[PP\x81`\x01\x1B\x91`\0\x19\x90`\x03\x1B\x1C\x19\x16\x17\x82U[` \x81\x01Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!W\x81\x90a\x0B:\x82a\x0B1`\x01\x88\x01Ta\x14\x92V[`\x01\x88\x01a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\x0E\nW`\0\x92a\r\xFFW[PP\x81`\x01\x1B\x91`\0\x19\x90`\x03\x1B\x1C\x19\x16\x17`\x01\x83\x01U[`@\x81\x01Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x0B\x98\x82a\x0B\x8F`\x02\x87\x01Ta\x14\x92V[`\x02\x87\x01a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\r\x8CW``\x93\x92\x91`\0\x91\x83a\r\x81W[PP\x81`\x01\x1B\x91`\0\x19\x90`\x03\x1B\x1C\x19\x16\x17`\x02\x84\x01U[\x01Q\x80Q\x90`\x01`\x01`@\x1B\x03\x82\x11a\x06!Wa\x0B\xF9\x82a\x0B\xF0`\x03\x86\x01Ta\x14\x92V[`\x03\x86\x01a\x17\x07V[` \x90`\x1F\x83\x11`\x01\x14a\r\x12W`\x03\x92\x91`\0\x91\x83a\r\x07W[PP\x81`\x01\x1B\x91`\0\x19\x90\x84\x1B\x1C\x19\x16\x17\x91\x01U[`\x02T\x90`\0R`\x03` R`@`\0 Ua\x0CE\x81\x83a\x16\xDCV[QQQ\x15\x15\x80a\x0C\xEFW[\x80a\x0C\xD7W[\x80a\x0C\xBFW[\x15a\x0CoWa\x0Cj\x90a\x16\xCDV[a\n.V[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\"`$\x82\x01R\x7FInvalid proof of address ownersh`D\x82\x01Ra\x06\x97`\xF4\x1B`d\x82\x01R`\x84\x90\xFD[P``a\x0C\xCC\x82\x84a\x16\xDCV[Q\x01QQ\x15\x15a\x0C\\V[P`@a\x0C\xE4\x82\x84a\x16\xDCV[Q\x01QQ\x15\x15a\x0CVV[P` a\x0C\xFC\x82\x84a\x16\xDCV[Q\x01QQ\x15\x15a\x0CPV[\x01Q\x90P\x88\x80a\x0C\x14V[\x90`\x03\x84\x01`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\riWP\x91\x83\x91`\x01\x93`\x03\x95`\x1F\x19\x81\x16\x10a\rQW[PPP\x81\x1B\x01\x91\x01Ua\x0C)V[\x01Q`\0\x19\x83\x86\x1B`\xF8\x16\x1C\x19\x16\x90U\x88\x80\x80a\rCV[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\r#V[\x01Q\x90P\x89\x80a\x0B\xB4V[\x90`\x02\x85\x01`\0R` `\0 \x91`\0[`\x1F\x19\x85\x16\x81\x10a\r\xE7WP\x91\x83\x91`\x01\x93``\x96\x95`\x1F\x19\x81\x16\x10a\r\xCEW[PPP\x81\x1B\x01`\x02\x84\x01Ua\x0B\xCCV[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x89\x80\x80a\r\xBEV[\x91\x92` `\x01\x81\x92\x86\x85\x01Q\x81U\x01\x94\x01\x92\x01a\r\x9DV[\x01Q\x90P\x88\x80a\x0BPV[\x92P`\x01\x85\x01`\0R` `\0 \x90`\0\x93[`\x1F\x19\x84\x16\x85\x10a\x0EaW`\x01\x94P\x83`\x1F\x19\x81\x16\x10a\x0EHW[PPP\x81\x1B\x01`\x01\x83\x01Ua\x0BhV[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x88\x80\x80a\x0E8V[\x81\x81\x01Q\x83U` \x94\x85\x01\x94`\x01\x90\x93\x01\x92\x90\x91\x01\x90a\x0E\x1DV[\x01Q\x90P\x88\x80a\n\xF3V[\x92P\x84`\0R` `\0 \x90`\0\x93[`\x1F\x19\x84\x16\x85\x10a\x0E\xD8W`\x01\x94P\x83`\x1F\x19\x81\x16\x10a\x0E\xBFW[PPP\x81\x1B\x01\x82Ua\x0B\x08V[\x01Q`\0\x19`\xF8\x84`\x03\x1B\x16\x1C\x19\x16\x90U\x88\x80\x80a\x0E\xB2V[\x81\x81\x01Q\x83U` \x94\x85\x01\x94`\x01\x90\x93\x01\x92\x90\x91\x01\x90a\x0E\x97V[cNH{q`\xE0\x1B`\0R`\0`\x04R`$`\0\xFD[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\x18`$\x82\x01R\x7FAddress already verified\0\0\0\0\0\0\0\0`D\x82\x01R`d\x90\xFD[P`@Q\x90` \x82\x01\x90` \x83RQ\x80\x91R`@\x82\x01\x90`@\x81`\x05\x1B\x84\x01\x01\x93\x91`\0\x90[\x82\x82\x10a\x0F\xA3W\x7F8#\x15\xD4\xD5j`5\xE1\x89\x9B\xFF\xE7}\x9B\xEC\xEF\xAF_&P\xE42;'\x85HW\xA0EFX\x85\x87\x03\x86\xA1\0[\x90\x91\x92\x94` \x80a\x0F\xC0`\x01\x93`?\x19\x89\x82\x03\x01\x86R\x89Qa\x13\xEBV[\x97\x01\x92\x01\x92\x01\x90\x92\x91a\x0FtV[\x835`\x01`\x01`@\x1B\x03\x81\x11a\x01XW\x82\x01`\x80`#\x19\x826\x03\x01\x12a\x01XW`@Q\x91a\x0F\xFB\x83a\x15bV[`$\x82\x015`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x10\x1E\x90`$6\x91\x85\x01\x01a\x15\xD0V[\x83R`D\x82\x015`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x10C\x90`$6\x91\x85\x01\x01a\x15\xD0V[` \x84\x01R`d\x82\x015`\x01`\x01`@\x1B\x03\x81\x11a\x01XWa\x10k\x90`$6\x91\x85\x01\x01a\x15\xD0V[`@\x84\x01R`\x84\x82\x015\x92`\x01`\x01`@\x1B\x03\x84\x11a\x01XWa\x10\x98` \x94\x93`$\x86\x956\x92\x01\x01a\x15\xD0V[``\x82\x01R\x81R\x01\x93\x01\x92a\n\x1AV[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\x02T\x81\x10\x15a\x01XWa\x10\xD2a\x11N\x91a\x14BV[Pa\x11x`\x03a\x11j`@Q\x93a\x10\xF4\x85a\x10\xED\x81\x84a\x14\xCCV[\x03\x86a\x15}V[a\x11\\`@Qa\x11\x12\x81a\x11\x0B\x81`\x01\x87\x01a\x14\xCCV[\x03\x82a\x15}V[a\x11:`@Q\x93a\x11*\x85a\x10\xED\x81`\x02\x85\x01a\x14\xCCV[a\x10\xED`@Q\x80\x98\x81\x93\x01a\x14\xCCV[`@Q\x97\x88\x97`\x80\x89R`\x80\x89\x01\x90a\x13\xC6V[\x90\x87\x82\x03` \x89\x01Ra\x13\xC6V[\x90\x85\x82\x03`@\x87\x01Ra\x13\xC6V[\x90\x83\x82\x03``\x85\x01Ra\x13\xC6V[\x03\x90\xF3[4a\x01XW`\x006`\x03\x19\x01\x12a\x01XW`\0T`@Q`\x01`\x01`\xA0\x1B\x03\x90\x91\x16\x81R` \x90\xF3[4a\x01XW`\x006`\x03\x19\x01\x12a\x01XW```\x01T`\xFF`@Q\x91a\xFF\xFF\x80\x82\x16\x84R\x81`\x10\x1C\x16` \x84\x01R` \x1C\x16`@\x82\x01R\xF3[4a\x01XW`\x006`\x03\x19\x01\x12a\x01XWa\x11\xF7a\x16uV[`\0\x80T`\x01`\x01`\xA0\x1B\x03\x19\x81\x16\x82U`\x01`\x01`\xA0\x1B\x03\x16\x7F\x8B\xE0\x07\x9CS\x16Y\x14\x13D\xCD\x1F\xD0\xA4\xF2\x84\x19I\x7F\x97\"\xA3\xDA\xAF\xE3\xB4\x18okdW\xE0\x82\x80\xA3\0[4a\x01XW` 6`\x03\x19\x01\x12a\x01XW`\x045`\0R`\x04` R` `@`\0 T`@Q\x90\x81R\xF3[4a\x01XW` \x80`\x03\x196\x01\x12a\x01XW`\x045a\x12\x81\x83a\x15bV[``\x80\x84\x81\x80\x96R\x81\x85\x82\x01R\x81`@\x82\x01R\x01R\x80`\0R`\x03\x82R`@`\0 T\x15a\x13gW`\0R`\x03\x81R`@`\0 T`\0\x19\x81\x01\x90\x81\x11a\x13QWa\x12\xCD`\x03\x91a\x14BV[P\x92a\x13:`@Q\x94a\x12\xDF\x86a\x15bV[`@Qa\x12\xF0\x81a\x11\x0B\x81\x85a\x14\xCCV[\x86R`@Qa\x13\x06\x81a\x11\x0B\x81`\x01\x86\x01a\x14\xCCV[\x85\x87\x01R`@Qa\x13\x1E\x81a\x11\x0B\x81`\x02\x86\x01a\x14\xCCV[`@\x87\x01Ra\x133`@Q\x80\x95\x81\x93\x01a\x14\xCCV[\x03\x83a\x15}V[\x83\x01Ra\x11x`@Q\x92\x82\x84\x93\x84R\x83\x01\x90a\x13\xEBV[cNH{q`\xE0\x1B`\0R`\x11`\x04R`$`\0\xFD[`@QbF\x1B\xCD`\xE5\x1B\x81R`\x04\x81\x01\x83\x90R`\x14`$\x82\x01Rs\x10Y\x19\x1C\x99\\\xDC\xC8\x1B\x9B\xDD\x08\x1D\x99\\\x9AY\x9AYY`b\x1B`D\x82\x01R`d\x90\xFD[`\0[\x83\x81\x10a\x13\xB6WPP`\0\x91\x01RV[\x81\x81\x01Q\x83\x82\x01R` \x01a\x13\xA6V[\x90` \x91a\x13\xDF\x81Q\x80\x92\x81\x85R\x85\x80\x86\x01\x91\x01a\x13\xA3V[`\x1F\x01`\x1F\x19\x16\x01\x01\x90V[a\x14?\x91``a\x14.a\x14\x1Ca\x14\n\x85Q`\x80\x86R`\x80\x86\x01\x90a\x13\xC6V[` \x86\x01Q\x85\x82\x03` \x87\x01Ra\x13\xC6V[`@\x85\x01Q\x84\x82\x03`@\x86\x01Ra\x13\xC6V[\x92\x01Q\x90``\x81\x84\x03\x91\x01Ra\x13\xC6V[\x90V[`\x02T\x81\x10\x15a\x14|W`\x02`\0R`\x02\x1B\x7F@W\x87\xFA\x12\xA8#\xE0\xF2\xB7c\x1C\xC4\x1B;\xA8\x82\x8B3!\xCA\x81\x11\x11\xFAu\xCD:\xA3\xBBZ\xCE\x01\x90`\0\x90V[cNH{q`\xE0\x1B`\0R`2`\x04R`$`\0\xFD[\x90`\x01\x82\x81\x1C\x92\x16\x80\x15a\x14\xC2W[` \x83\x10\x14a\x14\xACWV[cNH{q`\xE0\x1B`\0R`\"`\x04R`$`\0\xFD[\x91`\x7F\x16\x91a\x14\xA1V[\x90`\0\x92\x91\x80T\x91a\x14\xDD\x83a\x14\x92V[\x91\x82\x82R`\x01\x93\x84\x81\x16\x90\x81`\0\x14a\x15?WP`\x01\x14a\x14\xFFW[PPPPV[\x90\x91\x93\x94P`\0R` \x92\x83`\0 \x92\x84`\0\x94[\x83\x86\x10a\x15+WPPPP\x01\x01\x908\x80\x80\x80a\x14\xF9V[\x80T\x85\x87\x01\x83\x01R\x94\x01\x93\x85\x90\x82\x01a\x15\x14V[\x92\x94PPP` \x93\x94P`\xFF\x19\x16\x83\x83\x01R\x15\x15`\x05\x1B\x01\x01\x908\x80\x80\x80a\x14\xF9V[`\x80\x81\x01\x90\x81\x10`\x01`\x01`@\x1B\x03\x82\x11\x17a\x06!W`@RV[\x90`\x1F\x80\x19\x91\x01\x16\x81\x01\x90\x81\x10`\x01`\x01`@\x1B\x03\x82\x11\x17a\x06!W`@RV[`\x01`\x01`@\x1B\x03\x81\x11a\x06!W`\x05\x1B` \x01\x90V[`\x01`\x01`@\x1B\x03\x81\x11a\x06!W`\x1F\x01`\x1F\x19\x16` \x01\x90V[\x81`\x1F\x82\x01\x12\x15a\x01XW\x805\x90a\x15\xE7\x82a\x15\xB5V[\x92a\x15\xF5`@Q\x94\x85a\x15}V[\x82\x84R` \x83\x83\x01\x01\x11a\x01XW\x81`\0\x92` \x80\x93\x01\x83\x86\x017\x83\x01\x01R\x90V[\x81`\x1F\x82\x01\x12\x15a\x01XW\x805\x91a\x16.\x83a\x15\x9EV[\x92a\x16<`@Q\x94\x85a\x15}V[\x80\x84R` \x92\x83\x80\x86\x01\x92`\x05\x1B\x82\x01\x01\x92\x83\x11a\x01XW\x83\x01\x90[\x82\x82\x10a\x16fWPPPP\x90V[\x815\x81R\x90\x83\x01\x90\x83\x01a\x16XV[`\0T`\x01`\x01`\xA0\x1B\x03\x163\x03a\x16\x89WV[`d`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R` `$\x82\x01R\x7FOwnable: caller is not the owner`D\x82\x01R\xFD[`\0\x19\x81\x14a\x13QW`\x01\x01\x90V[\x80Q\x82\x10\x15a\x14|W` \x91`\x05\x1B\x01\x01\x90V[\x81\x81\x10a\x16\xFBWPPV[`\0\x81U`\x01\x01a\x16\xF0V[\x91\x90`\x1F\x81\x11a\x17\x16WPPPV[a\x17B\x92`\0R` `\0 \x90` `\x1F\x84\x01`\x05\x1C\x83\x01\x93\x10a\x17DW[`\x1F\x01`\x05\x1C\x01\x90a\x16\xF0V[V[\x90\x91P\x81\x90a\x175V[\x15a\x17UWV[`@QbF\x1B\xCD`\xE5\x1B\x81R` `\x04\x82\x01R`\x10`$\x82\x01Ro\x12[\x9D\x98[\x1AY\x08\x13T\xD5\x08\x1C\x9B\xDB\xDD`\x82\x1B`D\x82\x01R`d\x90\xFD[\x90a\x17\x97\x82a\x15\x9EV[a\x17\xA4`@Q\x91\x82a\x15}V[\x82\x81R\x80\x92a\x17\xB5`\x1F\x19\x91a\x15\x9EV[\x01\x90`\0[\x82\x81\x10a\x17\xC6WPPPV[\x80``` \x80\x93\x85\x01\x01R\x01a\x17\xBAV[\x90\x81Q\x80\x82R` \x80\x80\x93\x01\x93\x01\x91`\0[\x82\x81\x10a\x17\xF7WPPPP\x90V[\x83Q\x85R\x93\x81\x01\x93\x92\x81\x01\x92`\x01\x01a\x17\xE9V[\x90\x91`\0\x81\x81R`\x04\x93` \x93\x85\x85R`@\x93\x84\x84 T\x90\x83Q\x91`\x01\x92\x83\x10\x15a\x1A6W\x90a\x18B\x88\x94\x93\x92\x88\x87\x01Q\x14a\x17NV[`\x02\x82[a\x19tW[PPPa\x18u\x90a\x18\x87\x86Q\x94\x85\x93\x84\x93c\x1E\x8E\x1E\x13`\xE0\x1B\x85R\x89\x8C\x86\x01R`D\x85\x01\x90a\x13\xC6V[\x83\x81\x03`\x03\x19\x01`$\x85\x01R\x90a\x17\xD7V[\x03\x81\x7F\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0`\x01`\x01`\xA0\x1B\x03\x16Z\xFA\x82\x91\x81a\x198W[Pa\x190WP`d\x94P=\x15a\x19*W=\x90a\x18\xD8\x82a\x15\xB5V[\x91a\x18\xE5\x84Q\x93\x84a\x15}V[\x82R\x83=\x92\x01>[QbF\x1B\xCD`\xE5\x1B\x81R\x91\x82\x01R`\x17`$\x82\x01R\x7FInvalid inclusion proof\0\0\0\0\0\0\0\0\0`D\x82\x01R\xFD[Pa\x18\xEDV[\x93PPPP\x90V[\x90\x91P\x84\x81\x81=\x83\x11a\x19mW[a\x19P\x81\x83a\x15}V[\x81\x01\x03\x12a\x19iWQ\x80\x15\x15\x81\x03a\x19iW\x908a\x18\xBDV[\x82\x80\xFD[P=a\x19FV[\x90\x91\x92\x93\x85Q\x82\x10\x15a\x1A/WP\x81\x86R\x88\x88R\x86\x86 `\x01\x19\x90\x84\x01\x82\x82\x01\x83\x81\x11a\x1A\x1CW\x81T\x11\x15a\x1A\tW\x87R\x81\x89\x88 \x01\x01Ta\x19\xB6\x82\x87a\x16\xDCV[Q\x03a\x19\xCFW\x90a\x19\xC7\x83\x92a\x16\xCDV[\x88\x94\x93a\x18FV[\x86QbF\x1B\xCD`\xE5\x1B\x81R\x80\x8A\x01\x89\x90R`\x14`$\x82\x01RsInvalid root balance``\x1B`D\x82\x01R`d\x90\xFD[cNH{q`\xE0\x1B\x88R`2\x8BR`$\x88\xFD[cNH{q`\xE0\x1B\x89R`\x11\x8CR`$\x89\xFD[\x93\x92a\x18KV[cNH{q`\xE0\x1B\x86R`2\x89R`$\x86\xFD\xFE\xA2dipfsX\"\x12 Liu\0\x97k\x80\xEB\xFD\xB9L\x86\x19q0\xF8[Bw\xC7Ib\x08\xD4\x02\xA9\xE6'\x92PS\xF2dsolcC\0\x08\x12\x003";
    /// The deployed bytecode of the contract.
    pub static SUMMA_DEPLOYED_BYTECODE: ::ethers::core::types::Bytes = ::ethers::core::types::Bytes::from_static(
        __DEPLOYED_BYTECODE,
    );
    pub struct Summa<M>(::ethers::contract::Contract<M>);
    impl<M> ::core::clone::Clone for Summa<M> {
        fn clone(&self) -> Self {
            Self(::core::clone::Clone::clone(&self.0))
        }
    }
    impl<M> ::core::ops::Deref for Summa<M> {
        type Target = ::ethers::contract::Contract<M>;
        fn deref(&self) -> &Self::Target {
            &self.0
        }
    }
    impl<M> ::core::ops::DerefMut for Summa<M> {
        fn deref_mut(&mut self) -> &mut Self::Target {
            &mut self.0
        }
    }
    impl<M> ::core::fmt::Debug for Summa<M> {
        fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
            f.debug_tuple(::core::stringify!(Summa)).field(&self.address()).finish()
        }
    }
    impl<M: ::ethers::providers::Middleware> Summa<M> {
        /// Creates a new contract instance with the specified `ethers` client at
        /// `address`. The contract derefs to a `ethers::Contract` object.
        pub fn new<T: Into<::ethers::core::types::Address>>(
            address: T,
            client: ::std::sync::Arc<M>,
        ) -> Self {
            Self(
                ::ethers::contract::Contract::new(
                    address.into(),
                    SUMMA_ABI.clone(),
                    client,
                ),
            )
        }
        /// Constructs the general purpose `Deployer` instance based on the provided constructor arguments and sends it.
        /// Returns a new instance of a deployer that returns an instance of this contract after sending the transaction
        ///
        /// Notes:
        /// - If there are no constructor arguments, you should pass `()` as the argument.
        /// - The default poll duration is 7 seconds.
        /// - The default number of confirmations is 1 block.
        ///
        ///
        /// # Example
        ///
        /// Generate contract bindings with `abigen!` and deploy a new contract instance.
        ///
        /// *Note*: this requires a `bytecode` and `abi` object in the `greeter.json` artifact.
        ///
        /// ```ignore
        /// # async fn deploy<M: ethers::providers::Middleware>(client: ::std::sync::Arc<M>) {
        ///     abigen!(Greeter, "../greeter.json");
        ///
        ///    let greeter_contract = Greeter::deploy(client, "Hello world!".to_string()).unwrap().send().await.unwrap();
        ///    let msg = greeter_contract.greet().call().await.unwrap();
        /// # }
        /// ```
        pub fn deploy<T: ::ethers::core::abi::Tokenize>(
            client: ::std::sync::Arc<M>,
            constructor_args: T,
        ) -> ::core::result::Result<
            ::ethers::contract::builders::ContractDeployer<M, Self>,
            ::ethers::contract::ContractError<M>,
        > {
            let factory = ::ethers::contract::ContractFactory::new(
                SUMMA_ABI.clone(),
                SUMMA_BYTECODE.clone().into(),
                client,
            );
            let deployer = factory.deploy(constructor_args)?;
            let deployer = ::ethers::contract::ContractDeployer::new(deployer);
            Ok(deployer)
        }
        ///Calls the contract's `addressOwnershipProofs` (0xa3c4bcf8) function
        pub fn address_ownership_proofs(
            &self,
            p0: ::ethers::core::types::U256,
        ) -> ::ethers::contract::builders::ContractCall<
            M,
            (
                ::std::string::String,
                ::std::string::String,
                ::ethers::core::types::Bytes,
                ::ethers::core::types::Bytes,
            ),
        > {
            self.0
                .method_hash([163, 196, 188, 248], p0)
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `commitments` (0x49ce8997) function
        pub fn commitments(
            &self,
            p0: ::ethers::core::types::U256,
        ) -> ::ethers::contract::builders::ContractCall<M, ::ethers::core::types::U256> {
            self.0
                .method_hash([73, 206, 137, 151], p0)
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `config` (0x79502c55) function
        pub fn config(
            &self,
        ) -> ::ethers::contract::builders::ContractCall<M, (u16, u16, u8)> {
            self.0
                .method_hash([121, 80, 44, 85], ())
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `getAddressOwnershipProof` (0x19b33968) function
        pub fn get_address_ownership_proof(
            &self,
            address_hash: [u8; 32],
        ) -> ::ethers::contract::builders::ContractCall<M, AddressOwnershipProof> {
            self.0
                .method_hash([25, 179, 57, 104], address_hash)
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `owner` (0x8da5cb5b) function
        pub fn owner(
            &self,
        ) -> ::ethers::contract::builders::ContractCall<
            M,
            ::ethers::core::types::Address,
        > {
            self.0
                .method_hash([141, 165, 203, 91], ())
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `renounceOwnership` (0x715018a6) function
        pub fn renounce_ownership(
            &self,
        ) -> ::ethers::contract::builders::ContractCall<M, ()> {
            self.0
                .method_hash([113, 80, 24, 166], ())
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `submitCommitment` (0xda64a750) function
        pub fn submit_commitment(
            &self,
            mst_root: ::ethers::core::types::U256,
            root_balances: ::std::vec::Vec<::ethers::core::types::U256>,
            cryptocurrencies: ::std::vec::Vec<Cryptocurrency>,
            timestamp: ::ethers::core::types::U256,
        ) -> ::ethers::contract::builders::ContractCall<M, ()> {
            self.0
                .method_hash(
                    [218, 100, 167, 80],
                    (mst_root, root_balances, cryptocurrencies, timestamp),
                )
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `submitProofOfAddressOwnership` (0xc7ddca0e) function
        pub fn submit_proof_of_address_ownership(
            &self,
            address_ownership_proofs: ::std::vec::Vec<AddressOwnershipProof>,
        ) -> ::ethers::contract::builders::ContractCall<M, ()> {
            self.0
                .method_hash([199, 221, 202, 14], address_ownership_proofs)
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `transferOwnership` (0xf2fde38b) function
        pub fn transfer_ownership(
            &self,
            new_owner: ::ethers::core::types::Address,
        ) -> ::ethers::contract::builders::ContractCall<M, ()> {
            self.0
                .method_hash([242, 253, 227, 139], new_owner)
                .expect("method not found (this should never happen)")
        }
        ///Calls the contract's `verifyInclusionProof` (0xc8e58147) function
        pub fn verify_inclusion_proof(
            &self,
            proof: ::ethers::core::types::Bytes,
            public_inputs: ::std::vec::Vec<::ethers::core::types::U256>,
            timestamp: ::ethers::core::types::U256,
        ) -> ::ethers::contract::builders::ContractCall<M, bool> {
            self.0
                .method_hash([200, 229, 129, 71], (proof, public_inputs, timestamp))
                .expect("method not found (this should never happen)")
        }
        ///Gets the contract's `AddressOwnershipProofSubmitted` event
        pub fn address_ownership_proof_submitted_filter(
            &self,
        ) -> ::ethers::contract::builders::Event<
            ::std::sync::Arc<M>,
            M,
            AddressOwnershipProofSubmittedFilter,
        > {
            self.0.event()
        }
        ///Gets the contract's `LiabilitiesCommitmentSubmitted` event
        pub fn liabilities_commitment_submitted_filter(
            &self,
        ) -> ::ethers::contract::builders::Event<
            ::std::sync::Arc<M>,
            M,
            LiabilitiesCommitmentSubmittedFilter,
        > {
            self.0.event()
        }
        ///Gets the contract's `OwnershipTransferred` event
        pub fn ownership_transferred_filter(
            &self,
        ) -> ::ethers::contract::builders::Event<
            ::std::sync::Arc<M>,
            M,
            OwnershipTransferredFilter,
        > {
            self.0.event()
        }
        /// Returns an `Event` builder for all the events of this contract.
        pub fn events(
            &self,
        ) -> ::ethers::contract::builders::Event<::std::sync::Arc<M>, M, SummaEvents> {
            self.0.event_with_filter(::core::default::Default::default())
        }
    }
    impl<M: ::ethers::providers::Middleware> From<::ethers::contract::Contract<M>>
    for Summa<M> {
        fn from(contract: ::ethers::contract::Contract<M>) -> Self {
            Self::new(contract.address(), contract.client())
        }
    }
    #[derive(
        Clone,
        ::ethers::contract::EthEvent,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethevent(
        name = "AddressOwnershipProofSubmitted",
        abi = "AddressOwnershipProofSubmitted((string,string,bytes,bytes)[])"
    )]
    pub struct AddressOwnershipProofSubmittedFilter {
        pub address_ownership_proofs: ::std::vec::Vec<AddressOwnershipProof>,
    }
    #[derive(
        Clone,
        ::ethers::contract::EthEvent,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethevent(
        name = "LiabilitiesCommitmentSubmitted",
        abi = "LiabilitiesCommitmentSubmitted(uint256,uint256,uint256[],(string,string)[])"
    )]
    pub struct LiabilitiesCommitmentSubmittedFilter {
        #[ethevent(indexed)]
        pub timestamp: ::ethers::core::types::U256,
        pub mst_root: ::ethers::core::types::U256,
        pub root_balances: ::std::vec::Vec<::ethers::core::types::U256>,
        pub cryptocurrencies: ::std::vec::Vec<Cryptocurrency>,
    }
    #[derive(
        Clone,
        ::ethers::contract::EthEvent,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethevent(
        name = "OwnershipTransferred",
        abi = "OwnershipTransferred(address,address)"
    )]
    pub struct OwnershipTransferredFilter {
        #[ethevent(indexed)]
        pub previous_owner: ::ethers::core::types::Address,
        #[ethevent(indexed)]
        pub new_owner: ::ethers::core::types::Address,
    }
    ///Container type for all of the contract's events
    #[derive(Clone, ::ethers::contract::EthAbiType, Debug, PartialEq, Eq, Hash)]
    pub enum SummaEvents {
        AddressOwnershipProofSubmittedFilter(AddressOwnershipProofSubmittedFilter),
        LiabilitiesCommitmentSubmittedFilter(LiabilitiesCommitmentSubmittedFilter),
        OwnershipTransferredFilter(OwnershipTransferredFilter),
    }
    impl ::ethers::contract::EthLogDecode for SummaEvents {
        fn decode_log(
            log: &::ethers::core::abi::RawLog,
        ) -> ::core::result::Result<Self, ::ethers::core::abi::Error> {
            if let Ok(decoded) = AddressOwnershipProofSubmittedFilter::decode_log(log) {
                return Ok(SummaEvents::AddressOwnershipProofSubmittedFilter(decoded));
            }
            if let Ok(decoded) = LiabilitiesCommitmentSubmittedFilter::decode_log(log) {
                return Ok(SummaEvents::LiabilitiesCommitmentSubmittedFilter(decoded));
            }
            if let Ok(decoded) = OwnershipTransferredFilter::decode_log(log) {
                return Ok(SummaEvents::OwnershipTransferredFilter(decoded));
            }
            Err(::ethers::core::abi::Error::InvalidData)
        }
    }
    impl ::core::fmt::Display for SummaEvents {
        fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
            match self {
                Self::AddressOwnershipProofSubmittedFilter(element) => {
                    ::core::fmt::Display::fmt(element, f)
                }
                Self::LiabilitiesCommitmentSubmittedFilter(element) => {
                    ::core::fmt::Display::fmt(element, f)
                }
                Self::OwnershipTransferredFilter(element) => {
                    ::core::fmt::Display::fmt(element, f)
                }
            }
        }
    }
    impl ::core::convert::From<AddressOwnershipProofSubmittedFilter> for SummaEvents {
        fn from(value: AddressOwnershipProofSubmittedFilter) -> Self {
            Self::AddressOwnershipProofSubmittedFilter(value)
        }
    }
    impl ::core::convert::From<LiabilitiesCommitmentSubmittedFilter> for SummaEvents {
        fn from(value: LiabilitiesCommitmentSubmittedFilter) -> Self {
            Self::LiabilitiesCommitmentSubmittedFilter(value)
        }
    }
    impl ::core::convert::From<OwnershipTransferredFilter> for SummaEvents {
        fn from(value: OwnershipTransferredFilter) -> Self {
            Self::OwnershipTransferredFilter(value)
        }
    }
    ///Container type for all input parameters for the `addressOwnershipProofs` function with signature `addressOwnershipProofs(uint256)` and selector `0xa3c4bcf8`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(name = "addressOwnershipProofs", abi = "addressOwnershipProofs(uint256)")]
    pub struct AddressOwnershipProofsCall(pub ::ethers::core::types::U256);
    ///Container type for all input parameters for the `commitments` function with signature `commitments(uint256)` and selector `0x49ce8997`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(name = "commitments", abi = "commitments(uint256)")]
    pub struct CommitmentsCall(pub ::ethers::core::types::U256);
    ///Container type for all input parameters for the `config` function with signature `config()` and selector `0x79502c55`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(name = "config", abi = "config()")]
    pub struct ConfigCall;
    ///Container type for all input parameters for the `getAddressOwnershipProof` function with signature `getAddressOwnershipProof(bytes32)` and selector `0x19b33968`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(
        name = "getAddressOwnershipProof",
        abi = "getAddressOwnershipProof(bytes32)"
    )]
    pub struct GetAddressOwnershipProofCall {
        pub address_hash: [u8; 32],
    }
    ///Container type for all input parameters for the `owner` function with signature `owner()` and selector `0x8da5cb5b`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(name = "owner", abi = "owner()")]
    pub struct OwnerCall;
    ///Container type for all input parameters for the `renounceOwnership` function with signature `renounceOwnership()` and selector `0x715018a6`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(name = "renounceOwnership", abi = "renounceOwnership()")]
    pub struct RenounceOwnershipCall;
    ///Container type for all input parameters for the `submitCommitment` function with signature `submitCommitment(uint256,uint256[],(string,string)[],uint256)` and selector `0xda64a750`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(
        name = "submitCommitment",
        abi = "submitCommitment(uint256,uint256[],(string,string)[],uint256)"
    )]
    pub struct SubmitCommitmentCall {
        pub mst_root: ::ethers::core::types::U256,
        pub root_balances: ::std::vec::Vec<::ethers::core::types::U256>,
        pub cryptocurrencies: ::std::vec::Vec<Cryptocurrency>,
        pub timestamp: ::ethers::core::types::U256,
    }
    ///Container type for all input parameters for the `submitProofOfAddressOwnership` function with signature `submitProofOfAddressOwnership((string,string,bytes,bytes)[])` and selector `0xc7ddca0e`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(
        name = "submitProofOfAddressOwnership",
        abi = "submitProofOfAddressOwnership((string,string,bytes,bytes)[])"
    )]
    pub struct SubmitProofOfAddressOwnershipCall {
        pub address_ownership_proofs: ::std::vec::Vec<AddressOwnershipProof>,
    }
    ///Container type for all input parameters for the `transferOwnership` function with signature `transferOwnership(address)` and selector `0xf2fde38b`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(name = "transferOwnership", abi = "transferOwnership(address)")]
    pub struct TransferOwnershipCall {
        pub new_owner: ::ethers::core::types::Address,
    }
    ///Container type for all input parameters for the `verifyInclusionProof` function with signature `verifyInclusionProof(bytes,uint256[],uint256)` and selector `0xc8e58147`
    #[derive(
        Clone,
        ::ethers::contract::EthCall,
        ::ethers::contract::EthDisplay,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    #[ethcall(
        name = "verifyInclusionProof",
        abi = "verifyInclusionProof(bytes,uint256[],uint256)"
    )]
    pub struct VerifyInclusionProofCall {
        pub proof: ::ethers::core::types::Bytes,
        pub public_inputs: ::std::vec::Vec<::ethers::core::types::U256>,
        pub timestamp: ::ethers::core::types::U256,
    }
    ///Container type for all of the contract's call
    #[derive(Clone, ::ethers::contract::EthAbiType, Debug, PartialEq, Eq, Hash)]
    pub enum SummaCalls {
        AddressOwnershipProofs(AddressOwnershipProofsCall),
        Commitments(CommitmentsCall),
        Config(ConfigCall),
        GetAddressOwnershipProof(GetAddressOwnershipProofCall),
        Owner(OwnerCall),
        RenounceOwnership(RenounceOwnershipCall),
        SubmitCommitment(SubmitCommitmentCall),
        SubmitProofOfAddressOwnership(SubmitProofOfAddressOwnershipCall),
        TransferOwnership(TransferOwnershipCall),
        VerifyInclusionProof(VerifyInclusionProofCall),
    }
    impl ::ethers::core::abi::AbiDecode for SummaCalls {
        fn decode(
            data: impl AsRef<[u8]>,
        ) -> ::core::result::Result<Self, ::ethers::core::abi::AbiError> {
            let data = data.as_ref();
            if let Ok(decoded) = <AddressOwnershipProofsCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::AddressOwnershipProofs(decoded));
            }
            if let Ok(decoded) = <CommitmentsCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::Commitments(decoded));
            }
            if let Ok(decoded) = <ConfigCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::Config(decoded));
            }
            if let Ok(decoded) = <GetAddressOwnershipProofCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::GetAddressOwnershipProof(decoded));
            }
            if let Ok(decoded) = <OwnerCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::Owner(decoded));
            }
            if let Ok(decoded) = <RenounceOwnershipCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::RenounceOwnership(decoded));
            }
            if let Ok(decoded) = <SubmitCommitmentCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::SubmitCommitment(decoded));
            }
            if let Ok(decoded) = <SubmitProofOfAddressOwnershipCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::SubmitProofOfAddressOwnership(decoded));
            }
            if let Ok(decoded) = <TransferOwnershipCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::TransferOwnership(decoded));
            }
            if let Ok(decoded) = <VerifyInclusionProofCall as ::ethers::core::abi::AbiDecode>::decode(
                data,
            ) {
                return Ok(Self::VerifyInclusionProof(decoded));
            }
            Err(::ethers::core::abi::Error::InvalidData.into())
        }
    }
    impl ::ethers::core::abi::AbiEncode for SummaCalls {
        fn encode(self) -> Vec<u8> {
            match self {
                Self::AddressOwnershipProofs(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
                Self::Commitments(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
                Self::Config(element) => ::ethers::core::abi::AbiEncode::encode(element),
                Self::GetAddressOwnershipProof(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
                Self::Owner(element) => ::ethers::core::abi::AbiEncode::encode(element),
                Self::RenounceOwnership(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
                Self::SubmitCommitment(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
                Self::SubmitProofOfAddressOwnership(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
                Self::TransferOwnership(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
                Self::VerifyInclusionProof(element) => {
                    ::ethers::core::abi::AbiEncode::encode(element)
                }
            }
        }
    }
    impl ::core::fmt::Display for SummaCalls {
        fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
            match self {
                Self::AddressOwnershipProofs(element) => {
                    ::core::fmt::Display::fmt(element, f)
                }
                Self::Commitments(element) => ::core::fmt::Display::fmt(element, f),
                Self::Config(element) => ::core::fmt::Display::fmt(element, f),
                Self::GetAddressOwnershipProof(element) => {
                    ::core::fmt::Display::fmt(element, f)
                }
                Self::Owner(element) => ::core::fmt::Display::fmt(element, f),
                Self::RenounceOwnership(element) => ::core::fmt::Display::fmt(element, f),
                Self::SubmitCommitment(element) => ::core::fmt::Display::fmt(element, f),
                Self::SubmitProofOfAddressOwnership(element) => {
                    ::core::fmt::Display::fmt(element, f)
                }
                Self::TransferOwnership(element) => ::core::fmt::Display::fmt(element, f),
                Self::VerifyInclusionProof(element) => {
                    ::core::fmt::Display::fmt(element, f)
                }
            }
        }
    }
    impl ::core::convert::From<AddressOwnershipProofsCall> for SummaCalls {
        fn from(value: AddressOwnershipProofsCall) -> Self {
            Self::AddressOwnershipProofs(value)
        }
    }
    impl ::core::convert::From<CommitmentsCall> for SummaCalls {
        fn from(value: CommitmentsCall) -> Self {
            Self::Commitments(value)
        }
    }
    impl ::core::convert::From<ConfigCall> for SummaCalls {
        fn from(value: ConfigCall) -> Self {
            Self::Config(value)
        }
    }
    impl ::core::convert::From<GetAddressOwnershipProofCall> for SummaCalls {
        fn from(value: GetAddressOwnershipProofCall) -> Self {
            Self::GetAddressOwnershipProof(value)
        }
    }
    impl ::core::convert::From<OwnerCall> for SummaCalls {
        fn from(value: OwnerCall) -> Self {
            Self::Owner(value)
        }
    }
    impl ::core::convert::From<RenounceOwnershipCall> for SummaCalls {
        fn from(value: RenounceOwnershipCall) -> Self {
            Self::RenounceOwnership(value)
        }
    }
    impl ::core::convert::From<SubmitCommitmentCall> for SummaCalls {
        fn from(value: SubmitCommitmentCall) -> Self {
            Self::SubmitCommitment(value)
        }
    }
    impl ::core::convert::From<SubmitProofOfAddressOwnershipCall> for SummaCalls {
        fn from(value: SubmitProofOfAddressOwnershipCall) -> Self {
            Self::SubmitProofOfAddressOwnership(value)
        }
    }
    impl ::core::convert::From<TransferOwnershipCall> for SummaCalls {
        fn from(value: TransferOwnershipCall) -> Self {
            Self::TransferOwnership(value)
        }
    }
    impl ::core::convert::From<VerifyInclusionProofCall> for SummaCalls {
        fn from(value: VerifyInclusionProofCall) -> Self {
            Self::VerifyInclusionProof(value)
        }
    }
    ///Container type for all return fields from the `addressOwnershipProofs` function with signature `addressOwnershipProofs(uint256)` and selector `0xa3c4bcf8`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct AddressOwnershipProofsReturn {
        pub cex_address: ::std::string::String,
        pub chain: ::std::string::String,
        pub signature: ::ethers::core::types::Bytes,
        pub message: ::ethers::core::types::Bytes,
    }
    ///Container type for all return fields from the `commitments` function with signature `commitments(uint256)` and selector `0x49ce8997`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct CommitmentsReturn {
        pub mst_root: ::ethers::core::types::U256,
    }
    ///Container type for all return fields from the `config` function with signature `config()` and selector `0x79502c55`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct ConfigReturn {
        pub mst_levels: u16,
        pub currencies_count: u16,
        pub balance_byte_range: u8,
    }
    ///Container type for all return fields from the `getAddressOwnershipProof` function with signature `getAddressOwnershipProof(bytes32)` and selector `0x19b33968`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct GetAddressOwnershipProofReturn(pub AddressOwnershipProof);
    ///Container type for all return fields from the `owner` function with signature `owner()` and selector `0x8da5cb5b`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct OwnerReturn(pub ::ethers::core::types::Address);
    ///Container type for all return fields from the `verifyInclusionProof` function with signature `verifyInclusionProof(bytes,uint256[],uint256)` and selector `0xc8e58147`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct VerifyInclusionProofReturn(pub bool);
    ///`AddressOwnershipProof(string,string,bytes,bytes)`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct AddressOwnershipProof {
        pub cex_address: ::std::string::String,
        pub chain: ::std::string::String,
        pub signature: ::ethers::core::types::Bytes,
        pub message: ::ethers::core::types::Bytes,
    }
    ///`Cryptocurrency(string,string)`
    #[derive(
        Clone,
        ::ethers::contract::EthAbiType,
        ::ethers::contract::EthAbiCodec,
        Default,
        Debug,
        PartialEq,
        Eq,
        Hash
    )]
    pub struct Cryptocurrency {
        pub name: ::std::string::String,
        pub chain: ::std::string::String,
    }
}
