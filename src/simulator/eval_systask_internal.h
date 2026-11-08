#pragma once

#include <cstddef>
#include <cstdint>
#include <iosfwd>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"

namespace delta {

struct Expr;
struct Variable;
class SimContext;
class Arena;

Logic4Vec ScanStringToVec(Arena& arena, const std::string& str, uint32_t width);
void StoreRealField(Variable* var, Arena& arena, double d);
struct ScanRequest {
  const std::string& input;
  const std::string& fmt;
  Expr* const* dest;
  size_t ndest;
  size_t& consumed;
  SourceLoc loc;
  bool* hit_end = nullptr;
};

uint32_t RunScanf(const ScanRequest& req, SimContext& ctx, Arena& arena);

std::string ExtractStrArg(const Expr* arg);
std::string ExtractStringArg(const Expr* arg);
std::string EvalStringArg(const Expr* arg, SimContext& ctx, Arena& arena);
std::string FlattenHierPath(const Expr* arg);
std::vector<std::string> ScopeItemNames(const Expr* item,
                                        std::string_view caller);
std::optional<Logic4Vec> EvalCoverageSysCall(const Expr* expr, SimContext& ctx,
                                             Arena& arena,
                                             std::string_view name);

uint64_t TypedefBits(std::string_view name, SimContext& ctx, Arena& arena,
                     int depth = 0);
void WriteFileOutputTask(const Expr* expr, uint32_t descriptor,
                         std::string_view name, SimContext& ctx, Arena& arena);
Logic4Vec EvalFmonitor(const Expr* expr, uint32_t descriptor,
                       std::string_view name, SimContext& ctx, Arena& arena);
Logic4Vec EvalFstrobe(const Expr* expr, uint32_t descriptor,
                      std::string_view name, SimContext& ctx, Arena& arena);
std::string ResolveFormatArg(const Expr* arg, SimContext& ctx, Arena& arena);
size_t CountConsumingSpecifiers(const std::string& fmt);
void WarnIfArgCountMismatch(SimContext& ctx, std::string_view task_name,
                            const std::string& fmt, size_t supplied,
                            SourceLoc loc);

Logic4Vec EvalCastSysFunc(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalSscanf(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalReadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                      bool is_hex);
Logic4Vec EvalSreadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex);
Logic4Vec EvalWritemem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex);

Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena, std::string_view name);
Logic4Vec EvalTimescaleQuery(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name);
Logic4Vec EvalPrinttimescaleTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena);
Logic4Vec EvalTimeformatTask(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalTypename(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalTypenameOfExpression(const Expr* expr, SimContext& ctx,
                                   Arena& arena);

std::string ArrayArgPath(const Expr* arg0, SimContext& ctx, Arena& arena);

void EmitFinishDiagnostic(SimContext& ctx, std::string_view task, int64_t level,
                          std::ostream& os);

Logic4Vec EvalBits(const Expr* expr, SimContext& ctx, Arena& arena);

enum class UnpackedAggregateKind : uint8_t {
  kNone,
  kByteArray,
  kArray,
  kStruct,
};
UnpackedAggregateKind ClassifyUnpackedAggregate(const Expr* arg,
                                                SimContext& ctx);

}  // namespace delta
