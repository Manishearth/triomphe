fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rustc-check-cfg=cfg(triomphe_tsan)");

    // `cfg(sanitize)` is unstable, but Cargo exposes the target's cfg values to build scripts.
    let sanitizers = std::env::var("CARGO_CFG_SANITIZE").unwrap_or_default();
    if sanitizers.split(',').any(|s| s == "thread") {
        println!("cargo:rustc-cfg=triomphe_tsan");
    }
}
