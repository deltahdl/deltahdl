#ifndef DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_
#define DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "simulator/coverage_types.h"

namespace delta {

class Arena;
class SimContext;
struct ClassObject;
struct ClassTypeInfo;
struct CovergroupDecl;
struct EnumTypeInfo;
struct Expr;
struct ModuleItem;
struct RtlirVariable;
struct Stmt;
struct Variable;

// §19.6.3: the cross products an illegal_bins selection of a cross selects,
// each a tuple of indices into the bins of the crossed coverpoints; a sample
// that falls in one of them is a run-time error.
struct IllegalCrossProducts {
  std::string bins_name;
  std::vector<std::vector<size_t>> tuples;
};

// A coverpoint of an instance (§19.5), and what each sample reads for it.
struct SampledCoverpoint {
  CoverPoint* point = nullptr;
  const Expr* expr = nullptr;
  // §19.5: the guard the coverpoint is sampled under, null where none.
  const Expr* iff = nullptr;
  // §19.5: the type a sampled value is converted to, the coverpoint's data
  // type where one is written and else the self-determined type of its
  // expression.
  uint32_t width = 0;
  bool is_signed = false;
  bool is_real = false;
  // §19.5.3: whether that type holds x and z, so that a sample holding them
  // falls in no automatic bin, and the enumeration it is, null for none.
  bool is_four_state = true;
  const EnumTypeInfo* enum_type = nullptr;
  // §19.5.1: the guard of each bin whose definition ends in `iff`, by index
  // into the coverpoint's bins.
  std::vector<std::pair<size_t, const Expr*>> bin_guards;
  // §19.7 and §19.7.1: the coverpoint's options.
  CoverPointOption option;
  CoverPointTypeOption type_option;
};

// A cross of an instance (§19.6): its index into CoverGroup::crosses, the
// guards of the cross and of its bins, and its illegal_bins selections.
struct SampledCross {
  size_t index = 0;
  const Expr* iff = nullptr;
  std::vector<std::pair<size_t, const Expr*>> bin_guards;
  std::vector<IllegalCrossProducts> illegal;
};

// One instance of a covergroup (§19.3): the declaration it was built from,
// the coverage model CoverageDB keeps for it, and what sample() reads.
struct CovergroupInstance {
  const CovergroupDecl* decl = nullptr;
  CoverGroup* group = nullptr;
  // §19.3: the variable each formal names while the covergroup's expressions
  // are read, holding the actual new() gave it, or for a `ref` formal the
  // actual itself.
  std::vector<std::pair<std::string_view, Variable*>> formals;
  // §19.4: the object a covergroup embedded in a class belongs to, whose
  // members the covergroup's expressions read; null for any other covergroup.
  ClassObject* owner = nullptr;
  // §19.8.1: the formals of `with function sample`, as a function the
  // arguments of sample() are bound to; null where the covergroup has none.
  const ModuleItem* sample_function = nullptr;
  std::vector<SampledCoverpoint> points;
  std::vector<SampledCross> crosses;
};

// The covergroup instances a run's variables hold, keyed by the storage name
// of the variable, as the semaphores and mailboxes of SimContext are, or for
// an embedded covergroup by its object and name.
class CovergroupTable {
 public:
  CovergroupInstance* Create(std::string_view key);
  // The instance a reference to `name` denotes, searched in the order
  // SimContext::ScopedObjectKeys gives; null where `name` holds none.
  CovergroupInstance* Find(std::string_view name, const SimContext& ctx);
  // §19.4: the instance of the covergroup `name` embedded in `owner`'s class.
  CovergroupInstance* FindEmbedded(const ClassObject* owner,
                                   std::string_view name);
  static std::string EmbeddedKey(const ClassObject* owner,
                                 std::string_view name);
  // §19.3: records that the variable stored under `key` is of the covergroup
  // type `decl`, so that a `new` assigned to it later builds an instance.
  void Declare(std::string_view key, const CovergroupDecl* decl);
  // The key of the variable `name` denotes, searched as Find searches, with
  // the covergroup type Declare recorded for it; null where `name` is of none.
  const std::pair<const std::string, const CovergroupDecl*>* FindDeclared(
      std::string_view name, const SimContext& ctx) const;
  // §19.11.3: notes a built instance among those of its type, and the
  // instances of the covergroup type `decl`, in the order they were built.
  void Record(const CovergroupInstance& inst);
  std::vector<const CoverGroup*> InstancesOf(const CovergroupDecl* decl) const;
  // Whether any instance has been built, before which no call or option read
  // can reach one.
  bool Empty() const { return instances_.empty(); }
  // §19.4: the covergroup `name` that `type`, or a class it derives from,
  // embeds; null where none does. Each class's are read once.
  const CovergroupDecl* Embedded(const ClassTypeInfo* type,
                                 std::string_view name);

 private:
  std::unordered_map<std::string, CovergroupInstance> instances_;
  std::unordered_map<std::string, const CovergroupDecl*> declared_;
  std::vector<std::pair<const CovergroupDecl*, const CoverGroup*>> built_;
  std::unordered_map<
      const ClassTypeInfo*,
      std::vector<std::pair<std::string_view, const CovergroupDecl*>>>
      embedded_;
};

// §19.3 and §19.4: where a `new` of a covergroup builds its instance: the
// key the instance is kept under, the covergroup it is of, and for an
// embedded covergroup the object it belongs to, null for any other.
struct CovergroupSite {
  std::string key;
  const CovergroupDecl* decl = nullptr;
  ClassObject* owner = nullptr;
};

// §19.3 and §19.4: builds at `site` the instance a `new` of its covergroup
// makes, binding the covergroup's formals to the actuals of `new_call`, with
// the options, coverpoints, bins and crosses the declaration writes.
CovergroupInstance* BuildCovergroupInstance(const CovergroupSite& site,
                                            const Expr* new_call,
                                            SimContext& ctx, Arena& arena);

// §19.3: records the covergroup type of a variable `cg name ...;` and builds
// the instance its initializer `new(...)` makes, if it has one.
void CreateCovergroupForVar(std::string_view name, const RtlirVariable& var,
                            SimContext& ctx, Arena& arena);

// §19.3 and §19.4: a blocking assignment of `new` to a variable of a
// covergroup type, or in a class method to a covergroup the class embeds,
// builds the instance. False where the assignment is not one.
bool TryCovergroupNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §19.7: a blocking assignment to an instance option of a covergroup
// instance, `c.option.comment = ...;`, or of one of its coverpoints or
// crosses, `c.a.option.weight = ...;`, writes the option. False where the
// assignment is not one.
bool TryCovergroupOptionAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §19.8: sample(), get_coverage(), get_inst_coverage(), set_inst_name(),
// start() and stop() called through an instance, the coverage methods also
// through one of its coverpoints or crosses, and get_coverage() through the
// covergroup type. False where the call's receiver is none of these.
bool TryEvalCovergroupMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

// §19.7 and §19.10: a read of `option.member` or `type_option.member` through
// an instance, or through one of its coverpoints or crosses. False where the
// expression is not one.
bool TryEvalCovergroupOptionRead(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta

#endif  // DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_
