use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    let cuda_lib_dir = "../ntt-gpu";

    cc::Build::new()
        .cuda(true)
        .cudart("static")
        .include(cuda_lib_dir)
        .files(&[
            format!("{}/ntt.cu", cuda_lib_dir),
            format!("{}/utils.cu", cuda_lib_dir),
        ])
        .flag("-arch=sm_89")
        .warnings(false)
        .extra_warnings(false)
        .compile("ntt_gpu_stark");

    println!("cargo:rustc-link-lib=cudart");
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", cuda_lib_dir);

    Ok(())
}
