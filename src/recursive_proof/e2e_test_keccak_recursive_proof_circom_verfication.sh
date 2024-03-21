echo "****GENERATING RECURSIVE PLONKY2 KECCAK PROOF****"
cargo test -r --color=always --package Plonky2-lib   --lib keccak_test   --no-fail-fast -- -Z unstable-options --show-output
echo "DONE ($((end - start))s)"
cd scripts && ./run.sh && cd .. && cd ..