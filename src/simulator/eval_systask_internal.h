#pragma once

// Internal declarations shared among the eval_systask*.cpp translation units.
// These helpers and task evaluators are private to the system-task evaluator
// and are not part of the public evaluation.h surface. Each symbol is defined
// in exactly one .cpp; this header only carries the declarations needed where
// one system-task file calls into another.

#include <string>
#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

// String/format-argument helpers (defined in eval_systask.cpp).
std::string ExtractStrArg(const Expr* arg);
std::string EvalStringArg(const Expr* arg, SimContext& ctx, Arena& arena);
std::string ResolveFormatArg(const Expr* arg, SimContext& ctx, Arena& arena);
size_t CountConsumingSpecifiers(const std::string& fmt);
void WarnIfArgCountMismatch(SimContext& ctx, std::string_view task_name,
                            const std::string& fmt, size_t supplied);

// §21.4 / §21.5 / §D.14 memory load/dump tasks (defined in
// eval_systask_readmem.cpp); called by the EvalIOSysCall dispatcher.
Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                      bool is_hex);
Logic4Vec EvalSreadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex);
Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex);

}  // namespace delta
