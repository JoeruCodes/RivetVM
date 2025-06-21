use std::fs;

use app::vm::{
    witness::{evaluate_constraints, generate_vm_witness},
    TraceEntry,
};

#[test]
fn run_all_vm_cases() {
    let workspace = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap();
    let cases_root = workspace.join("r2vm_cases");
    if !cases_root.exists() {
        panic!("No cases found – run scripts/build_case.sh first");
    }

    for entry in fs::read_dir(&cases_root).unwrap() {
        let dir = entry.unwrap().path();
        if !dir.is_dir() {
            continue;
        }
        let ll_path = dir.join(format!("{}.ll", dir.file_name().unwrap().to_string_lossy()));
        let trace_path = dir.join("trace.json");
        let mem_path = dir.join("memory_trace.json");
        let other_cols_path = dir.join("other_cols.json");

        println!("Running VM constraints for case: {}", dir.display());
        let llvm_ir = fs::read_to_string(&ll_path).expect("read ll");
        let trace_data = fs::read_to_string(&trace_path).expect("trace.json");
        let memory_trace_data = fs::read_to_string(&mem_path).expect("memory_trace.json");
        let other_cols_raw = fs::read(&other_cols_path).expect("other_cols.json");
        let trace: Vec<TraceEntry> = serde_json::from_str(&trace_data).expect("parse trace");
        let trace_len = trace.len();

        let trace_columns =
            generate_vm_witness(&llvm_ir, &trace_data, &memory_trace_data, &other_cols_raw)
                .expect("witness");
        evaluate_constraints(trace_columns, &llvm_ir, trace_len).expect("constraints");
    }
}
