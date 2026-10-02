#ifndef DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_
#define DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/coverage_types.h"

namespace delta {

class Arena;
class SimContext;
struct ModuleItem;
struct CoverCrossDecl;
struct CoverPointDecl;
struct CovergroupInstance;
struct CoverageOption;
struct CovergroupValueRange;
struct Expr;
struct SampledCoverpoint;

// A call whose actuals a CovergroupFrame binds to the formals of `function`:
// new()'s to the covergroup's own (§19.3), sample()'s to those of `with
// function sample` (§19.8.1).
struct CovergroupCall {
  const ModuleItem* function = nullptr;
  const Expr* call = nullptr;
};

// §19.3 and §19.4: while it stands, the expressions of a covergroup are read
// in the covergroup's own scope. The actuals of `calls` are bound to their
// formals, read where the call was made; then the covergroup's formals name
// what CovergroupInstance binds them to, a name of the scope that called
// sample() or new() is no longer seen, and an embedded covergroup reads the
// members of the object it belongs to.
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

// The integral and the real value of an expression a covergroup reads.
int64_t CovergroupInt(const Expr* e, SimContext& ctx, Arena& arena);
double CovergroupReal(const Expr* e, SimContext& ctx, Arena& arena);

// The values of a coverpoint's type, which a `$` bound of a range (§19.5.1),
// a `with` on the coverpoint's name (§19.5.1.1) and its automatic bins
// (§19.5.3) span.
CoverValueRange PointTypeBounds(const SampledCoverpoint& point);

// §19.5.1: the values of a covergroup_range_list in the order written, a `$`
// bound standing for the end of the coverpoint's values.
std::vector<CoverValueRange> CovergroupRangeValues(
    const std::vector<CovergroupValueRange>& ranges,
    const SampledCoverpoint& point, SimContext& ctx, Arena& arena);

// §19.5: `v` as the coverpoint's type holds it, the value converted as though
// assigned to a variable of that type.
int64_t ConvertToPointType(const Logic4Vec& v, const SampledCoverpoint& point);

// §19.5: adds to an instance whose group options are in place the coverpoint
// `decl` declares, its options applied and its bins built. `index` is the
// coverpoint's position among the covergroup's items, which names one that
// has no label and samples no single variable.
void BuildCoverpoint(CovergroupInstance& inst, const CoverPointDecl& decl,
                     size_t index, SimContext& ctx, Arena& arena);

// §19.5 to §19.5.6: the bins of a coverpoint, and of a real one, built from
// its declaration in an instance whose coverpoint options are in place.
void BuildCoverpointBins(CovergroupInstance& inst, SampledCoverpoint& point,
                         const CoverPointDecl& decl, SimContext& ctx,
                         Arena& arena);

// §19.6 to §19.6.3: the cross `decl` of an instance whose coverpoints are
// built, given an implicit coverpoint for each variable it crosses directly.
// `index` is the cross's position among the covergroup's items, which names
// an unlabelled one.
void BuildCross(CovergroupInstance& inst, const CoverCrossDecl& decl,
                size_t index, SimContext& ctx, Arena& arena);

// §19.7 and §19.7.1: applies an option assignment of the covergroup, of the
// coverpoint `point` or of the cross `cross` to the instance.
void ApplyGroupOption(CovergroupInstance& inst, const CoverageOption& option,
                      SimContext& ctx, Arena& arena);
void ApplyPointOption(SampledCoverpoint& point, const CoverageOption& option,
                      SimContext& ctx, Arena& arena);
void ApplyCrossOption(CrossCover& cross, const CoverageOption& option,
                      SimContext& ctx, Arena& arena);

// §19.7 and §19.10: the value of the option `member`, a type option where
// `type_option` holds, of the covergroup, the coverpoint or the cross; false
// where the level has no such option.
bool ReadGroupOption(const CoverGroup& group, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);
bool ReadPointOption(const SampledCoverpoint& point, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);
bool ReadCrossOption(const CrossCover& cross, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);

}  // namespace delta

#endif  // DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_
