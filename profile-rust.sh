cargo build --release --manifest-path rust-derp/Cargo.toml && time perf record -g ./rust-derp/target/release/derp ttt.derp
