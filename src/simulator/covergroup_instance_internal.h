#ifndef DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_
#define DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "simulator/coverage_types.h"

namespace delta {

class Arena;
class DiagEngine;
class SimContext;
struct ModuleItem;
struct ClassObject;
struct CoverCrossDecl;
struct CoverPointDecl;
struct CovergroupDecl;
struct CovergroupInstance;
struct CoverageOption;
struct CovergroupValueRange;
struct Expr;
struct SampledCoverpoint;
struct SampledCross;
struct Stmt;
struct TypeOptionWrite;

struct CovergroupCall {
  const ModuleItem* function = nullptr;
  const Expr* call = nullptr;
};

class CovergroupFrame {
 public:
  CovergroupFrame(const CovergroupInstance& inst, SimContext& ctx, Arena& arena,
                  const std::vector<CovergroupCall>& calls = {});
  ~CovergroupFrame();
  CovergroupFrame(const CovergroupFrame&) = delete;
  CovergroupFrame& operator=(const CovergroupFrame&) = delete;

 private:
  SimContext& ctx_;
  bool pushed_this_ = false;
};

ClassObject* ObjectNamed(const Expr* e, SimContext& ctx, Arena& arena);

int64_t CovergroupInt(const Expr* e, SimContext& ctx, Arena& arena);
double CovergroupReal(const Expr* e, SimContext& ctx, Arena& arena);
int64_t CovergroupIntOf(const Logic4Vec& v);
double CovergroupRealOf(const Logic4Vec& v);

CoverValueRange PointTypeBounds(const SampledCoverpoint& point);

std::vector<CoverValueRange> CovergroupRangeValues(
    const std::vector<CovergroupValueRange>& ranges,
    const SampledCoverpoint& point, SimContext& ctx, Arena& arena);

std::vector<CoverValueRange> NormalizeSpans(std::vector<CoverValueRange> list);

int64_t ConvertToPointType(const Logic4Vec& v, const SampledCoverpoint& point);
int64_t ConvertToPointType(uint64_t bits, const SampledCoverpoint& point);

void BuildCoverpoint(CovergroupInstance& inst, const CoverPointDecl& decl,
                     size_t index, SimContext& ctx, Arena& arena);

void BuildCoverpointBins(CovergroupInstance& inst, SampledCoverpoint& point,
                         const CoverPointDecl& decl, SimContext& ctx,
                         Arena& arena);

void WarnOfBinOverlaps(const CoverPoint& cp,
                       const std::vector<SourceLoc>& origins, DiagEngine& diag);

void BuildCross(CovergroupInstance& inst, const CoverCrossDecl& decl,
                size_t index, SimContext& ctx, Arena& arena);

void ApplyGroupOption(CovergroupInstance& inst, const CoverageOption& option,
                      SimContext& ctx, Arena& arena);
void ApplyPointOption(SampledCoverpoint& point, const CoverageOption& option,
                      SimContext& ctx, Arena& arena);
void ApplyCrossOption(CrossCover& cross, const CoverageOption& option,
                      SimContext& ctx, Arena& arena);

bool OptionValueAccepted(std::string_view member, const Logic4Vec& value,
                         SourceLoc at, SimContext& ctx);

void WriteGroupOption(CovergroupInstance& inst, std::string_view member,
                      const Logic4Vec& value);
void WritePointOption(SampledCoverpoint& point, std::string_view member,
                      const Logic4Vec& value);
void WriteCrossOption(CovergroupInstance& inst, SampledCross& cross,
                      std::string_view member, const Logic4Vec& value);

bool ReadGroupOption(const CoverGroup& group, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);
bool ReadPointOption(const SampledCoverpoint& point, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);
bool ReadCrossOption(const CrossCover& cross, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);

std::string CoverpointName(const CoverPointDecl& cp, size_t index);

void SetTypeOption(CovergroupInstance& inst, const TypeOptionWrite& write);

bool ReadTypeOption(const CovergroupInstance& inst, std::string_view item,
                    std::string_view member, Arena& arena, Logic4Vec& out);

const CovergroupDecl* TypeOptionOwner(const Expr* access, SimContext& ctx,
                                      std::string& item);

bool TryCovergroupTypeOptionAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

bool TryEvalCovergroupTypeOptionRead(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out);

struct CovergroupTarget {
  CovergroupInstance* inst = nullptr;
  SampledCoverpoint* point = nullptr;
  SampledCross* cross = nullptr;
};

Logic4Vec ReportCoverage(const CovergroupTarget& target, const Expr* call,
                         bool instance, SimContext& ctx, Arena& arena);

bool TryEvalTypeCoverageCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

}  // namespace delta

#endif
