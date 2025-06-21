#!/usr/bin/env bash
# fix_traces.sh -- Fix trace files for all test cases

set -euo pipefail

CASES=("hello" "arithmetic" "control" "recursive" "memory")

for case in "${CASES[@]}"; do
    echo "Processing case: $case"
    
    # Run the build script
    ../scripts/build_case.sh "../examples/${case}.c"
    
    # Manually move the trace files
    mv "starks-v2/r2vm/trace.json" "starks-v2/r2vm_cases/${case}/trace.json"
    mv "starks-v2/r2vm/memory_trace.json" "starks-v2/r2vm_cases/${case}/memory_trace.json"
    mv "starks-v2/r2vm/other_cols.json" "starks-v2/r2vm_cases/${case}/other_cols.json"
    
    echo "✅ Fixed trace files for $case"
done

echo "🎉 All trace files fixed!" 