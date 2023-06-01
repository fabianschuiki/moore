// Copyright (c) 2016-2021 Fabian Schuiki

use std::{
    env,
    ffi::OsStr,
    path::{Path, PathBuf},
    process::Command,
};

fn target_env_is(name: &str) -> bool {
    match env::var_os("CARGO_CFG_TARGET_ENV") {
        Some(s) => s == name,
        None => false,
    }
}

fn target_os_is(name: &str) -> bool {
    match env::var_os("CARGO_CFG_TARGET_OS") {
        Some(s) => s == name,
        None => false,
    }
}

fn llvm_config_run(binary: impl AsRef<OsStr>, arg: &str) -> String {
    let output = Command::new(binary)
        .arg(arg)
        .arg("--link-static")
        .output()
        .expect("llvm-config run failed");
    String::from_utf8(output.stdout)
        .expect("Output from llvm-config was not valid UTF-8")
        .trim()
        .to_string()
}

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

    // Locate `llvm-config` to figure out what to link.
    let llvm_config_bin = llvm_build_dir.join("bin").join("llvm-config");
    let llvm_lib_dir = llvm_config_run(&llvm_config_bin, "--libdir");
    let llvm_include_dir = llvm_config_run(&llvm_config_bin, "--includedir");

    // Library search paths
    let lib_dirs = [
        circt_build_dir.join("lib"),
        Path::new(llvm_lib_dir.as_str()).to_owned(),
    ];
    for name in &lib_dirs {
        println!("cargo:rustc-link-search=native={}", name.display());
    }

    // CIRCT/LLVM/MLIR libraries
    let lib_names = [
        "CIRCTCAPIComb",
        "CIRCTCAPIHW",
        "CIRCTCAPILLHD",
        "CIRCTCAPIMoore",
        "CIRCTCAPISV",
        "CIRCTCAPISeq",
        "CIRCTComb",
        "CIRCTHW",
        "CIRCTLLHD",
        "CIRCTMoore",
        "CIRCTSV",
        "CIRCTSeq",
        "CIRCTSupport",
        "LLVMBinaryFormat",
        "LLVMBitstreamReader",
        "LLVMCore",
        "LLVMDemangle",
        "LLVMRemarks",
        "LLVMSupport",
        "MLIRAnalysis",
        "MLIRArithDialect",
        "MLIRArithValueBoundsOpInterfaceImpl",
        "MLIRCAPIFunc",
        "MLIRCAPIIR",
        "MLIRCAPIControlFlow",
        "MLIRCallInterfaces",
        "MLIRControlFlowDialect",
        "MLIRControlFlowInterfaces",
        "MLIRFuncDialect",
        "MLIRIR",
        "MLIRInferTypeOpInterface",
        "MLIRInferIntRangeCommon",
        "MLIRInferIntRangeInterface",
        "MLIRPDLToPDLInterp",
        "MLIRParser",
        "MLIRPass",
        "MLIRRewrite",
        "MLIRSideEffectInterfaces",
        "MLIRSupport",
        "MLIRTransformUtils",
        "MLIRTransforms",
    ];
    for name in &lib_names {
        println!("cargo:rustc-link-lib=static={}", name);
    }

    // Ensure we trigger a rebuild if the libraries change, which is useful for
    // development.
    for lib_dir in &lib_dirs {
        for name in &lib_names {
            let path = lib_dir.join(format!("lib{}.a", name));
            if path.exists() {
                println!("cargo:rerun-if-changed={}", path.display());
            }
        }
    }

    // Get the library that must be linked for C++, if any.
    // Soruce: https://gitlab.com/taricorp/llvm-sys.rs/-/blob/main/build.rs
    let system_libcpp = if target_env_is("msvc") {
        None
    } else if target_os_is("macos") || target_os_is("freebsd") {
        Some("c++")
    } else {
        Some("stdc++")
    };
    if let Some(system_libcpp) = system_libcpp {
        println!("cargo:rustc-link-lib=dylib={}", system_libcpp);
    }

    // Link against system libraries needed for LLVM
    for mut arg in llvm_config_run(llvm_config_bin, "--system-libs").split(&[' ', '\n']) {
        if arg.is_empty() {
            continue;
        }
        arg = arg.strip_prefix("-llib").unwrap_or(arg);
        arg = arg.strip_prefix("-l").unwrap_or(arg);
        arg = arg.strip_suffix(".tbd").unwrap_or(arg); // macos
        arg = arg.strip_suffix(".lib").unwrap_or(arg); // msvc
        println!("cargo:rustc-link-lib=dylib={}", arg);
    }

    // Make a list of include directories.
    let include_dirs = vec![
        circt_dir.join("include").display().to_string(),
        circt_build_dir.join("include").display().to_string(),
        llvm_include_dir,
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
