#ifndef DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_
#define DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct CoverGroup;
struct CoverPointDecl;
struct CovergroupDecl;
struct Expr;
struct RtlirVariable;

// §19.6.3: an illegal_bins selection of a cross, kept as the values its
// `binsof ( cover_point ) intersect { ... }` admits for one of the cross's
// coverpoints; a sampled tuple whose value of that coverpoint is one of them
// falls in the selection.
struct IllegalCrossSelection {
  std::string cross_name;
  std::string bins_name;
  std::string cover_point;
  std::vector<int64_t> values;
};

// One instance of a covergroup (§19.3): the declaration it was built from,
// the coverage model CoverageDB keeps for it, and what sample() reads.
struct CovergroupInstance {
  const CovergroupDecl* decl = nullptr;
  CoverGroup* group = nullptr;
  // §19.3: the value each formal took from new()'s actuals.
  std::unordered_map<std::string_view, int64_t> formals;
  // The expression each coverpoint samples, under the coverpoint's name.
  std::vector<std::pair<std::string, const Expr*>> points;
  std::vector<IllegalCrossSelection> illegal_selections;
};

// The covergroup instances a run's variables hold, keyed by the storage name
// of the variable, as the semaphores and mailboxes of SimContext are.
class CovergroupTable {
 public:
  CovergroupInstance* Create(std::string_view key);
  // The instance a reference to `name` denotes, searched in the order
  // SimContext::ScopedObjectKeys gives; null where `name` holds none.
  CovergroupInstance* Find(std::string_view name, const SimContext& ctx);

 private:
  std::unordered_map<std::string, CovergroupInstance> instances_;
};

// §19.3: builds the instance a declaration `cg name = new(...)` makes, with
// the coverpoints, bins and crosses the covergroup's declaration writes.
void CreateCovergroupForVar(std::string_view name, const RtlirVariable& var,
                            SimContext& ctx, Arena& arena);

// §19.8: sample(), get_coverage(), get_inst_coverage(), start() and stop()
// called through a variable holding a covergroup instance. False where the
// call's receiver holds no covergroup instance.
bool TryEvalCovergroupMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta

#endif  // DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_
