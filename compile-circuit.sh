#!/bin/bash
COMPILE_KECCAK_CHAIN=${1}
if [ ! -d "circuit" ]; then
    mkdir circuit
    cd circuit
    npm install
    cd ..
fi

if [ "$COMPILE_KECCAK_CHAIN" = "true" ]; then
    circom ./circuit/keccak-chain.circom --r1cs --json --sym --wasm --prime bn128 --output ./circuit/
fi

circom ./circuit/circuit2.circom --r1cs --json --sym --wasm --prime bn128 --output ./circuit/
circom ./circuit/circuit3.circom --r1cs --json --sym --wasm --prime bn128 --output ./circuit/
circom ./circuit/cubic_circuit.circom --r1cs --json --sym --wasm --prime bn128 --output ./circuit/
