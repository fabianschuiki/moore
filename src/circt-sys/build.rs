// Copyright (c) 2016-2021 Fabian Schuiki

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
    let lib_dirs = [circt_build_dir.join("lib"), llvm_build_dir.join("lib")];
    let lib_names = [
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
        "LLVMBinaryFormat",
        "LLVMBitstreamReader",
        "LLVMCore",
        "LLVMRemarks",
        "LLVMSupport",
        "MLIRAnalysis",
        "MLIRArithmetic",
        "MLIRCAPIFunc",
        "MLIRCAPIIR",
        "MLIRCAPIControlFlow",
        "MLIRCallInterfaces",
        "MLIRControlFlow",
        "MLIRControlFlowInterfaces",
        "MLIRFunc",
        "MLIRIR",
        "MLIRInferTypeOpInterface",
        "MLIRPDL",
        "MLIRPDLInterp",
        "MLIRPDLToPDLInterp",
        "MLIRParser",
        "MLIRPass",
        "MLIRRewrite",
        "MLIRSideEffectInterfaces",
        "MLIRSupport",
        "MLIRTransformUtils",
        "MLIRTransforms",
        "MLIRTranslation",
    ];
    for name in &lib_dirs {
        println!("cargo:rustc-link-search=native={}", name.display());
    }
    for name in &lib_names {
        println!("cargo:rustc-link-lib=static={}", name);
    }
    for lib_dir in &lib_dirs {
        for name in &lib_names {
            let path = lib_dir.join(format!("lib{}.a", name));
            if path.exists() {
                println!("cargo:rerun-if-changed={}", path.display());
            }
        }
    }

    // System libraries
    let system_libraries = [
        "stdc++", // llvm-config --system-libs --link-static
        "rt", "dl", "pthread", "m", "z", "tinfo",
    ];
    for name in &system_libraries {
        println!("cargo:rustc-link-lib=dylib={}", name);
    }

    // Make a list of include directories.
    let include_dirs = vec![
        circt_dir.join("include").display().to_string(),
        circt_build_dir.join("include").display().to_string(),
        llvm_dir.join("llvm/include").display().to_string(),
        llvm_dir.join("mlir/include").display().to_string(),
        llvm_build_dir.join("include").display().to_string(),
        llvm_build_dir
            .join("tools/mlir/include")
            .display()
            .to_string(),
    ];

    // Bindings
    println!("cargo:rerun-if-changed=wrapper.h");
    let mut bindings = bindgen::Builder::default().header("wrapper.h");
    for dir in &include_dirs {
        bindings = bindings.clang_arg("-I").clang_arg(dir);
    }
    let bindings = bindings
        .parse_callbacks(Box::new(bindgen::CargoCallbacks))
        .generate()
        .expect("Unable to generate bindings");

    // Write the bindings to the $OUT_DIR/bindings.rs file.
    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    // Additional wrapper code
    println!("cargo:rerun-if-changed=wrapper.cpp");
    cc::Build::new()
        .cpp(true)
        .file("wrapper.cpp")
        .includes(&include_dirs)
        .warnings(false)
        .extra_warnings(false)
        .compile("circt-sys-wrapper");
}
