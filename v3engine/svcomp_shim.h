// svcomp_shim.h
#pragma once

// CPAchecker’s default reachability spec: prove that __VERIFIER_error() is never called.
extern void __VERIFIER_error(void) __attribute__((noreturn));

// Map CBMC's assert to SV-COMP style error call.
#define __CPROVER_assert(cond, msg) do { \
if (!(cond)) __VERIFIER_error();       \
} while (0)

// Map your nondet to SV-COMP nondet (CPAchecker understands this symbol).
extern _Bool __VERIFIER_nondet_bool(void);
#define nondet_bool __VERIFIER_nondet_bool
