1. need to install circom, refer to: https://docs.circom.io/getting-started/installation.
2. need to install rapidsnark beside this repo. install refer to README.md of repo https://github.com/iden3/rapidsnark.
3. need to install snark beside this repo. clone repo https://github.com/iden3/snarkjs and use 
```
npm i
```

4. need to download powersOfTau28_hez_final_25.ptau in folder ~/Downloads. the powersOfTau28_hez_final_25 link is https://storage.googleapis.com/zkevm/ptau/powersOfTau28_hez_final_25.ptau.
5. need install packages of js in folder src/recursive_proof and src/recursive_proof/scripts/hardhat. use 

```
npm i
```

6. now can run script e2e_test_keccak_recursive_proof_circom_verfication.sh for an e2e_test of keccak circuit.
