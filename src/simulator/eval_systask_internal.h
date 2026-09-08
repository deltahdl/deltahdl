#pragma once

// Internal declarations shared among the eval_systask*.cpp translation units.
// These helpers and task evaluators are private to the system-task evaluator
// and are not part of the public evaluation.h surface. Each symbol is defined
// in exactly one .cpp; this header only carries the declarations needed where
// one system-task file calls into another.

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"
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
// §21.3.4.3 scan operation: the control string `fmt`, the `input` text it is
// matched against, the window of unevaluated destination expressions (`dest`
// holds `ndest` items, the arguments following the format string), and the
// out-param `consumed` reporting how much of `input` the scan absorbed.
struct ScanRequest {
  const std::string& input;
  const std::string& fmt;
  Expr* const* dest;
  size_t ndest;
  size_t& consumed;
  // Where the call was written. The scan renders %m through FormatDisplay,
  // which reports a format specifier it cannot apply, and the destinations are
  // the only expressions the scan holds -- a specifier consuming none of them
  // has no expression to name.
  SourceLoc loc;
  // §21.3.8 out-param (optional): set true when the scan attempted to read at
  // or past the end of `input` -- a delimiter look-ahead, a field or literal
  // that failed for lack of input, or a white-space directive that ran off the
  // end. An exact-count conversion (%c/%u/%z) that stops exactly at the end
  // never looks past what it takes, so it does not raise the flag. $fscanf
  // uses this to keep end-of-file detection observable by $feof.
  bool* hit_end = nullptr;
};

// scanf control-string engine: interprets `req.fmt` against `req.input`,
// assigning converted fields to the destination arguments; returns the number
// of items assigned and reports the consumed input length via `req.consumed`.
uint32_t RunScanf(const ScanRequest& req, SimContext& ctx, Arena& arena);

// String/format-argument helpers (defined in eval_systask.cpp).
std::string ExtractStrArg(const Expr* arg);
// Strips the surrounding quotes from a string-literal argument, returning any
// other argument's text unchanged. Defined in eval_system_func.cpp, where
// Annex D's $log uses it on the file name it opens; the §20.4.3 $timeformat
// suffix_string in eval_systask_time.cpp is unquoted the same way.
std::string ExtractStringArg(const Expr* arg);
std::string EvalStringArg(const Expr* arg, SimContext& ctx, Arena& arena);
std::string ResolveFormatArg(const Expr* arg, SimContext& ctx, Arena& arena);
size_t CountConsumingSpecifiers(const std::string& fmt);
// `loc` is where the call was written, which the warning names: the count is
// compared against a format string already reduced to text, so no expression
// survives to take a position from.
void WarnIfArgCountMismatch(SimContext& ctx, std::string_view task_name,
                            const std::string& fmt, size_t supplied,
                            SourceLoc loc);

// §21.3.4 formatted string read (defined in eval_systask_scanf.cpp); called
// by the EvalIOSysCall dispatcher.
Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena);

// §21.4 / §21.5 / §D.14 memory load/dump tasks (defined in
// eval_systask_readmem.cpp); called by the EvalIOSysCall dispatcher.
Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                      bool is_hex);
Logic4Vec EvalSreadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex);
Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex);

// §20.3 simulation time functions and §20.4 timescale tasks (defined in
// eval_systask_time.cpp); called by the EvalMiscSysCall dispatcher in
// eval_system_func.cpp.
//
// $time, $stime and $realtime; `name` selects which, and each reports the
// current time in the invoking module's time unit.
Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena, std::string_view name);
// §20.4.1 $timeunit and $timeprecision; `name` selects which.
Logic4Vec EvalTimescaleQuery(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name);
// §20.4.2 $printtimescale.
Logic4Vec EvalPrinttimescaleTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena);
// §20.4.3 $timeformat.
Logic4Vec EvalTimeformatTask(const Expr* expr, SimContext& ctx, Arena& arena);

}  // namespace delta
