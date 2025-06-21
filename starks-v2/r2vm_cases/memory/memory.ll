; ModuleID = '/home/joel/snarks/examples/memory.c'
source_filename = "/home/joel/snarks/examples/memory.c"
target datalayout = "e-m:e-p:64:64-i64:64-i128:128-n64-S128"
target triple = "riscv64-unknown-linux-gnu"

@arr = dso_local global [5 x i32] zeroinitializer, align 4

; Function Attrs: noinline nounwind optnone
define dso_local signext i32 @main() #0 {
  %1 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  store volatile i32 1, i32* getelementptr inbounds ([5 x i32], [5 x i32]* @arr, i64 0, i64 0), align 4
  store volatile i32 2, i32* getelementptr inbounds ([5 x i32], [5 x i32]* @arr, i64 0, i64 1), align 4
  %2 = load volatile i32, i32* getelementptr inbounds ([5 x i32], [5 x i32]* @arr, i64 0, i64 0), align 4
  %3 = load volatile i32, i32* getelementptr inbounds ([5 x i32], [5 x i32]* @arr, i64 0, i64 1), align 4
  %4 = add nsw i32 %2, %3
  store volatile i32 %4, i32* getelementptr inbounds ([5 x i32], [5 x i32]* @arr, i64 0, i64 2), align 4
  %5 = load volatile i32, i32* getelementptr inbounds ([5 x i32], [5 x i32]* @arr, i64 0, i64 2), align 4
  ret i32 %5
}

attributes #0 = { noinline nounwind optnone "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-features"="+64bit,+a,+c,+d,+f,+m" }

!llvm.module.flags = !{!0, !1, !2, !3, !4, !5}
!llvm.ident = !{!6}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 1, !"target-abi", !"lp64d"}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{i32 7, !"PIE Level", i32 2}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{i32 1, !"SmallDataLimit", i32 8}
!6 = !{!"Ubuntu clang version 14.0.0-1ubuntu1.1"}
