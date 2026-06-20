#pragma once

// Internal declarations shared among the eval_systask*.cpp translation units.
// These helpers and task evaluators are private to the system-task evaluator
// and are not part of the public evaluation.h surface. Each symbol is defined
// in exactly one .cpp; this header only carries the declarations needed where
// one system-task file calls into another.

#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
struct Variable;
class SimContext;
class Arena;

// §21.3.4.3 scanf helpers shared between $fscanf/$sscanf (eval_systask_io.cpp)
// and the file-I/O evaluator (eval_fileio.cpp). All defined in
// eval_systask_io.cpp.
//
// ScanStringToVec packs a matched string/character field into a destination,
// placing the leftmost character in the most significant byte.
Logic4Vec ScanStringToVec(Arena& arena, const std::string& str, uint32_t width);
// Stores a converted real value (its IEEE-754 bit pattern) into a real
// destination variable.
void StoreRealField(Variable* var, Arena& arena, double d);
// scanf control-string engine: interprets `fmt` against `input`, assigning
// converted fields to the destination arguments; returns the number of items
// assigned and reports the consumed input length via `consumed`.
uint32_t RunScanf(const std::string& input, const std::string& fmt,
                  Expr* const* dest, size_t ndest, SimContext& ctx,
                  Arena& arena, size_t& consumed);

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
