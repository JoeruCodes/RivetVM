use once_cell::sync::Lazy;
use serde_json;
use std::collections::HashMap;

pub static SSA_TO_COL_MAP: Lazy<HashMap<String, usize>> = Lazy::new(|| {
    serde_json::from_slice(include_bytes!("../../app/src/vm/ssa_map.json"))
        .expect("failed to parse ssa_map.json")
});

#[inline(always)]
pub fn record(tracer: &mut crate::trace::Tracer, ssa_name: &str, value: u128) {
    if let Some(col_idx) = SSA_TO_COL_MAP.get(ssa_name) {
        if *col_idx >= 32 {
            tracer.record_other(*col_idx - 32, value);
        }
    }
}
