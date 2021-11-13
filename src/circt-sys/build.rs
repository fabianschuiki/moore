use std::env;
use std::path::PathBuf;

fn main() {
    static ENV_CIRCT_DIR: &str = "CIRCT_SYS_CIRCT_DIR";
    static ENV_CIRCT_BUILD_DIR: &str = "CIRCT_SYS_CIRCT_BUILD_DIR";
    static ENV_LLVM_DIR: &str = "CIRCT_SYS_LLVM_DIR";
    static ENV_LLVM_BUILD_DIR: &str = "CIRCT_SYS_LLVM_BUILD_DIR";

    println!("cargo:rerun-if-env-changed={}", &*ENV_CIRCT_DIR);
    println!("cargo:rerun-if-env-changed={}", &*ENV_CIRCT_BUILD_DIR);
    println!("cargo:rerun-if-env-changed={}", &*ENV_LLVM_DIR);
    println!("cargo:rerun-if-env-changed={}", &*ENV_LLVM_BUILD_DIR);

    let circt_dir = PathBuf::from(env::var(ENV_CIRCT_DIR).unwrap());
    let circt_build_dir = env::var(ENV_CIRCT_BUILD_DIR)
        .map(PathBuf::from)
        .unwrap_or_else(|_| circt_dir.join("build"));
    let llvm_dir = env::var(ENV_LLVM_DIR)
        .map(PathBuf::from)
        .unwrap_or_else(|_| circt_dir.join("llvm"));
    let llvm_build_dir = env::var(ENV_LLVM_BUILD_DIR)
        .map(PathBuf::from)
        .unwrap_or_else(|_| llvm_dir.join("build"));

    // CIRCT/LLVM/MLIR libraries
    for name in &[circt_build_dir.join("lib"), llvm_build_dir.join("lib")] {
        println!("cargo:rustc-link-search=native={}", name.display());
    }
    for name in &[
        "CIRCTCAPIComb",
        "CIRCTCAPIHW",
        "CIRCTCAPILLHD",
        "CIRCTCAPISV",
        "CIRCTCAPISeq",
        "CIRCTComb",
        "CIRCTHW",
        "CIRCTLLHD",
        "CIRCTSV",
        "CIRCTSeq",
        "LLVMCore",
        "LLVMSupport",
        "MLIRAnalysis",
        "MLIRCAPIIR",
        "MLIRCAPIStandard",
        "MLIRIR",
        "MLIRPDL",
        "MLIRPDLInterp",
        "MLIRPDLToPDLInterp",
        "MLIRPass",
        "MLIRRewrite",
        "MLIRControlFlowInterfaces",
        "MLIRSideEffectInterfaces",
        "MLIRCallInterfaces",
        "MLIRSupport",
        "MLIRTransformUtils",
        "MLIRStandard",
        "MLIRTransforms",
        "MLIRTranslation",
    ] {
        println!("cargo:rustc-link-lib=static={}", name);
    }

    // System libraries
    let system_libraries = [
        "stdc++", // llvm-config --system-libs --link-static
        "rt", "dl", "pthread", "m", "z", "tinfo", "xml2",
    ];
    for name in &system_libraries {
        println!("cargo:rustc-link-lib=dylib={}", name);
    }

    // Bindings
    println!("cargo:rerun-if-changed=wrapper.h");
    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_arg("-I")
        .clang_arg(circt_dir.join("include").display().to_string())
        .clang_arg("-I")
        .clang_arg(circt_build_dir.join("include").display().to_string())
        .clang_arg("-I")
        .clang_arg(llvm_dir.join("llvm/include").display().to_string())
        .clang_arg("-I")
        .clang_arg(llvm_dir.join("mlir/include").display().to_string())
        .clang_arg("-I")
        .clang_arg(llvm_build_dir.join("include").display().to_string())
        .clang_arg("-I")
        .clang_arg(
            llvm_build_dir
                .join("tools/mlir/include")
                .display()
                .to_string(),
        )
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
