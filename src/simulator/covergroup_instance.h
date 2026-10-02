#ifndef DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_
#define DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_

#include <cstddef>
#include <cstdint>
#include <list>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/types.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_covergroup.h"
#include "simulator/coverage_types.h"

namespace delta {

class Arena;
class SimContext;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
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
  // §19.5: the width the expression is evaluated at, as though assigned to a
  // variable of the coverpoint's integral data type; 0 where none is written.
  uint32_t assigned_width = 0;
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
  // §19.3 with §23.6 and §27.4: the module instance, and where a process
  // built the instance the generate block instances, of the scope `new` ran
  // in, where the covergroup's expressions are read however the instance is
  // reached.
  std::string inst_prefix;
  std::vector<std::string> gen_prefixes;
  bool built_by_process = false;
  // §27.4: the implicit localparams of the loop generate blocks the variable
  // holding the instance is declared in, which the covergroup's expressions
  // read; null outside any.
  const GenBlockConsts* gen_consts = nullptr;
  std::vector<SampledCoverpoint> points;
  std::vector<SampledCross> crosses;
  // §19.7.1: whether a strobed sample is waiting in the Postponed region of
  // the current time slot, so that further occurrences of the clocking event
  // in the slot add none.
  bool strobe_pending = false;
};

// The covergroup instances of a run. §19.3: a variable of a covergroup type
// holds a handle to the instance `new` built, its identity, so that a copy of
// the handle or a formal it is passed to reaches the same instance; each
// `new` builds a fresh one. §19.4: an embedded covergroup's instance is kept
// by its object and name, its one `new` in the class's constructor.
class CovergroupTable {
 public:
  // A fresh instance, for an embedded covergroup (`embedded`) the one kept
  // under `key`, built again where one is.
  CovergroupInstance* Create(std::string_view key, bool embedded);
  // The identity a variable holding `inst`, an instance Create made, stores,
  // and the instance a stored identity refers to, null for the null handle or
  // a value of no instance.
  // An identity carries a tag no class handle reaches, so a class handle read
  // as one refers to no instance, and fits the 32-bit carrier of a class
  // property.
  uint64_t IdentityOf(const CovergroupInstance* inst) const;
  CovergroupInstance* Held(uint64_t identity) const;
  // §19.4: the instance of the covergroup `name` embedded in `owner`'s class.
  CovergroupInstance* FindEmbedded(const ClassObject* owner,
                                   std::string_view name);
  static std::string EmbeddedKey(const ClassObject* owner,
                                 std::string_view name);
  // §19.3: records that the variable `v`, or the array it carries the
  // elements of, is of the covergroup type `decl`, so that a `new` assigned
  // to it later builds an instance; and the type recorded, null for none.
  void Declare(const Variable* v, const CovergroupDecl* decl);
  const CovergroupDecl* DeclaredOf(const Variable* v) const;
  // §19.11.3: notes a built instance among those of its type, and the
  // instances of the covergroup type `decl`, in the order they were built.
  void Record(const CovergroupInstance& inst);
  std::vector<const CoverGroup*> InstancesOf(const CovergroupDecl* decl) const;
  // §19.3: notes an instance whose covergroup is sampled at a block event,
  // with the instance prefix of the scope it was built in, once however often
  // the instance is rebuilt.
  void WatchBlockEvents(CovergroupInstance* inst, std::string scope);
  const std::vector<std::pair<std::string, CovergroupInstance*>>&
  BlockEventWatchers() const {
    return block_watchers_;
  }
  // Whether any instance has been built, before which no call or option read
  // can reach one.
  bool Empty() const { return instances_.empty(); }
  // §19.4: the covergroup `name` that `type`, or a class it derives from,
  // embeds; null where none does. Each class's are read once.
  const CovergroupDecl* Embedded(const ClassTypeInfo* type,
                                 std::string_view name);

 private:
  std::unordered_map<std::string, CovergroupInstance> instances_;
  std::unordered_map<uint64_t, CovergroupInstance*> held_;
  std::unordered_map<const CovergroupInstance*, uint64_t> identities_;
  std::unordered_map<const Variable*, const CovergroupDecl*> declared_;
  std::vector<std::pair<const CovergroupDecl*, const CoverGroup*>> built_;
  std::vector<std::pair<std::string, CovergroupInstance*>> block_watchers_;
  std::unordered_map<
      const ClassTypeInfo*,
      std::vector<std::pair<std::string_view, const CovergroupDecl*>>>
      embedded_;
  // §19.4.1: the covergroups a derived covergroup amounts to, its base's
  // items it does not override and its own (EmbeddedCovergroups).
  std::list<CovergroupDecl> composed_;
};

// §19.3 and §19.4: where a `new` of a covergroup builds its instance: the
// key the instance is kept under, the covergroup it is of, and for an
// embedded covergroup the object it belongs to, null for any other.
struct CovergroupSite {
  std::string key;
  const CovergroupDecl* decl = nullptr;
  ClassObject* owner = nullptr;
  const GenBlockConsts* gen_consts = nullptr;
};

// §19.3 and §19.4: builds at `site` the instance a `new` of its covergroup
// makes, binding the covergroup's formals to the actuals of `new_call`, with
// the options, coverpoints, bins and crosses the declaration writes.
CovergroupInstance* BuildCovergroupInstance(const CovergroupSite& site,
                                            const Expr* new_call,
                                            SimContext& ctx, Arena& arena);

// §19.3: records the covergroup type of a variable `cg name ...;` and builds
// the instance its initializer `new(...)` makes, if it has one, storing its
// handle in `v`.
void CreateCovergroupForVar(std::string_view name, const RtlirVariable& var,
                            Variable* v, SimContext& ctx, Arena& arena);

// §19.3: the covergroup a declared type names, one a module, interface or
// program declares by its bare name, or a package's behind its scope or
// imported; null for any other type.
const CovergroupDecl* CovergroupOfType(const DataType& type, SimContext& ctx);

// §19.3: a variable `v` of a subroutine or block declared of a covergroup
// type `type`, its handle built by an initializer `new(...)`, `init`, where
// there is one. False where `type` is of no covergroup.
bool TryCreateCovergroupLocal(const DataType& type, const Expr* init,
                              Variable* v, SimContext& ctx, Arena& arena);

// §19.3 and §19.4: a blocking assignment of `new` to a variable of a
// covergroup type, an element of an array of them, a property or static
// property of one, or in a class method to a covergroup the class embeds,
// builds the instance. False where the assignment is not one.
bool TryCovergroupNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §19.3 with §8.7: the handle the declaration initializer `init`, a call of
// `new(...)`, gives the property `name` of `type` where the property is of a
// covergroup type: the instance built for it. None for any other property.
std::optional<Logic4Vec> CovergroupPropertyNew(const ClassTypeInfo* type,
                                               std::string_view name,
                                               const Expr* init,
                                               SimContext& ctx, Arena& arena);

// §19.7: a blocking assignment to an instance option of a covergroup
// instance, `c.option.comment = ...;`, or of one of its coverpoints or
// crosses, `c.a.option.weight = ...;`, writes the option. False where the
// assignment is not one.
bool TryCovergroupOptionAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §19.3: a covergroup whose coverage event is a block_event_expression is
// sampled as a task, function or block one of its terms names begins
// (`is_begin`) or ends. Called as the scope named `scope` is entered or left,
// it samples each such instance built in the running instance.
void SampleAtBlockEvent(std::string_view scope, bool is_begin, SimContext& ctx,
                        Arena& arena);

// §19.8: sample(), get_coverage(), get_inst_coverage(), set_inst_name(),
// start() and stop() called through an instance, the coverage methods also
// through one of its coverpoints or crosses, and get_coverage() through the
// covergroup type. False where the call's receiver is none of these.
bool TryEvalCovergroupMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

// §19.8 with §8.6: a covergroup method called on the handle a receiver that
// is a call already produced, `pick().sample()`. False where `handle` refers
// to no instance or the method is none of a covergroup's.
bool TryEvalCovergroupMethodOnHandle(const Logic4Vec& handle, const Expr* expr,
                                     SimContext& ctx, Arena& arena,
                                     Logic4Vec& out);

// §19.7 and §19.10: a read of `option.member` or `type_option.member` through
// an instance, or through one of its coverpoints or crosses. False where the
// expression is not one.
bool TryEvalCovergroupOptionRead(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta

#endif  // DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_
