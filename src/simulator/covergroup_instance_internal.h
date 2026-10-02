#ifndef DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_
#define DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "simulator/coverage_types.h"

namespace delta {

class Arena;
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

// The integral and the real value of an expression a covergroup reads, and
// of a value it reads.
// The object an expression naming a class handle holds; null where it names
// none. Only a name is read, so that no expression is evaluated for its side
// effects.
ClassObject* ObjectNamed(const Expr* e, SimContext& ctx, Arena& arena);

int64_t CovergroupInt(const Expr* e, SimContext& ctx, Arena& arena);
double CovergroupReal(const Expr* e, SimContext& ctx, Arena& arena);
int64_t CovergroupIntOf(const Logic4Vec& v);
double CovergroupRealOf(const Logic4Vec& v);

// The values of a coverpoint's type, which a `$` bound of a range (§19.5.1),
// a `with` on the coverpoint's name (§19.5.1.1) and its automatic bins
// (§19.5.3) span.
CoverValueRange PointTypeBounds(const SampledCoverpoint& point);

// §19.5.1: the values of a covergroup_range_list in the order written, a `$`
// bound standing for the end of the coverpoint's values.
std::vector<CoverValueRange> CovergroupRangeValues(
    const std::vector<CovergroupValueRange>& ranges,
    const SampledCoverpoint& point, SimContext& ctx, Arena& arena);

// `list` sorted, its overlapping and adjacent spans joined.
std::vector<CoverValueRange> NormalizeSpans(std::vector<CoverValueRange> list);

// §19.5: `v` as the coverpoint's type holds it, the value converted as though
// assigned to a variable of that type.
int64_t ConvertToPointType(const Logic4Vec& v, const SampledCoverpoint& point);
int64_t ConvertToPointType(uint64_t bits, const SampledCoverpoint& point);

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

// §19.7: writes `value` to the instance option `member` of the covergroup,
// the coverpoint `point` or the cross `cross`, where `member` is one that an
// assignment after instantiation may set: name, weight, goal, comment,
// at_least and cross_num_print_missing. A coverpoint's or a cross's new
// weight and at_least take effect in its coverage at once. Written to the
// covergroup, at_least and cross_num_print_missing are the default of each
// coverpoint and cross that does not set its own.
void WriteGroupOption(CovergroupInstance& inst, std::string_view member,
                      const Logic4Vec& value);
void WritePointOption(SampledCoverpoint& point, std::string_view member,
                      const Logic4Vec& value);
void WriteCrossOption(CovergroupInstance& inst, SampledCross& cross,
                      std::string_view member, const Logic4Vec& value);

// §19.7 and §19.10: the value of the option `member`, a type option where
// `type_option` holds, of the covergroup, the coverpoint or the cross; false
// where the level has no such option.
bool ReadGroupOption(const CoverGroup& group, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);
bool ReadPointOption(const SampledCoverpoint& point, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);
bool ReadCrossOption(const CrossCover& cross, bool type_option,
                     std::string_view member, Arena& arena, Logic4Vec& out);

// §19.5: the name a coverpoint goes by, its label or, unlabelled, the variable
// its expression names; any other is given its position `index` among the
// covergroup's items.
std::string CoverpointName(const CoverPointDecl& cp, size_t index);

// §19.7.1: writes a type option written through the covergroup type to the
// instance `inst` of it, at the covergroup level where `write.item` is empty
// and else to its coverpoint or cross of that name.
void SetTypeOption(CovergroupInstance& inst, const TypeOptionWrite& write);

// §19.7.1: the value of the type option `member` of the instance `inst`, of
// the covergroup where `item` is empty and else of its coverpoint or cross
// `item`; false where there is no such option.
bool ReadTypeOption(const CovergroupInstance& inst, std::string_view item,
                    std::string_view member, Arena& arena, Logic4Vec& out);

// §19.7.1 and §19.8: the covergroup type that `cg::type_option` or
// `cg::x::type_option`, `access`, is reached through, with x stored in `item`;
// null where `access` is none of these.
const CovergroupDecl* TypeOptionOwner(const Expr* access, SimContext& ctx,
                                      std::string& item);

// §19.7.1: a blocking assignment to a type option through the covergroup
// type, `cg::type_option.comment = ...;` or `cg::x::type_option.weight =
// ...;`, writes it to every instance of the type, built or to be built;
// strobe and real_interval, set in the definition only, are left as they are.
// False where the assignment is not one.
bool TryCovergroupTypeOptionAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

// §19.7.1: a read of `cg::type_option.member` or `cg::x::type_option.member`,
// taken from an instance of the type. False where the expression is not one or
// no instance of the type has been built.
bool TryEvalCovergroupTypeOptionRead(const Expr* expr, SimContext& ctx,
                                     Arena& arena, Logic4Vec& out);

// What a call or an option read reaches: an instance, or one of its
// coverpoints or crosses.
struct CovergroupTarget {
  CovergroupInstance* inst = nullptr;
  SampledCoverpoint* point = nullptr;
  SampledCross* cross = nullptr;
};

// Defined in covergroup_instance_coverage.cpp. §19.8 and §19.11:
// get_coverage() answers for the covergroup type, and get_inst_coverage() for
// the instance, or for its type where the merge_instances type option is set
// and the get_inst_coverage option is not (§19.7, Table 19-1); through a
// coverpoint or a cross, each answers for that item. The call's ref-int pair
// receives the covered and defined bins.
Logic4Vec ReportCoverage(const CovergroupTarget& target, const Expr* call,
                         bool instance, SimContext& ctx, Arena& arena);

// Defined in covergroup_instance_coverage.cpp. §19.8: `cg::get_coverage()`,
// the coverage of the covergroup type `cg`, and `cg::x::get_coverage()`, that
// of its coverpoint or cross x over every instance. False for any other call.
bool TryEvalTypeCoverageCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

}  // namespace delta

#endif  // DELTA_SIMULATOR_COVERGROUP_INSTANCE_INTERNAL_H_
