#ifndef DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_
#define DELTA_SIMULATOR_COVERGROUP_INSTANCE_H_

#include <cstddef>
#include <cstdint>
#include <map>
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

struct IllegalCrossProducts {
  std::string bins_name;
  std::vector<std::vector<size_t>> tuples;
};

struct SampledCoverpoint {
  CoverPoint* point = nullptr;
  const Expr* expr = nullptr;
  const Expr* iff = nullptr;
  uint32_t width = 0;
  bool is_signed = false;
  bool is_real = false;
  bool is_four_state = true;
  const EnumTypeInfo* enum_type = nullptr;
  uint32_t assigned_width = 0;
  std::vector<std::pair<size_t, const Expr*>> bin_guards;
  CoverPointOption option;
  CoverPointTypeOption type_option;
  std::vector<std::string_view> own_options;
};

struct SampledCross {
  size_t index = 0;
  const Expr* iff = nullptr;
  std::vector<std::pair<size_t, const Expr*>> bin_guards;
  std::vector<IllegalCrossProducts> illegal;
  std::vector<std::string_view> own_options;
};

struct CovergroupInstance {
  const CovergroupDecl* decl = nullptr;
  CoverGroup* group = nullptr;
  std::vector<std::pair<std::string_view, Variable*>> formals;
  ClassObject* owner = nullptr;
  const ClassTypeInfo* declaring_class = nullptr;
  const ModuleItem* sample_function = nullptr;
  std::string inst_prefix;
  std::vector<std::string> gen_prefixes;
  bool built_by_process = false;
  const GenBlockConsts* gen_consts = nullptr;
  std::vector<SampledCoverpoint> points;
  std::vector<SampledCross> crosses;
  bool strobe_pending = false;
};

struct TypeOptionWrite {
  const CovergroupDecl* decl = nullptr;
  std::string item;
  std::string member;
  Logic4Vec value;
};

using ComposedCovergroups =
    std::map<std::pair<const CovergroupDecl*, const CovergroupDecl*>,
             CovergroupDecl>;

class CovergroupTable {
 public:
  CovergroupInstance* Create(std::string_view key, bool embedded);
  uint64_t IdentityOf(const CovergroupInstance* inst) const;
  CovergroupInstance* Held(uint64_t identity) const;
  CovergroupInstance* FindEmbedded(const ClassObject* owner,
                                   std::string_view name);
  static std::string EmbeddedKey(const ClassObject* owner,
                                 std::string_view name);
  void Declare(const Variable* v, const CovergroupDecl* decl);
  const CovergroupDecl* DeclaredOf(const Variable* v) const;
  void Record(const CovergroupInstance& inst);
  std::vector<const CoverGroup*> InstancesOf(
      const CovergroupDecl* decl, const ClassTypeInfo* declaring_class) const;
  void WatchBlockEvents(CovergroupInstance* inst, std::string scope);
  const std::vector<std::pair<std::string, CovergroupInstance*>>&
  BlockEventWatchers() const {
    return block_watchers_;
  }
  bool Empty() const { return instances_.empty(); }
  const CovergroupDecl* Embedded(const ClassTypeInfo* type,
                                 std::string_view name);
  const ClassTypeInfo* DeclaringClass(const ClassTypeInfo* type,
                                      const CovergroupDecl* decl);
  void WriteTypeOption(TypeOptionWrite write);
  void TakeTypeOptionWrites(CovergroupInstance& inst) const;
  const std::vector<TypeOptionWrite>& TypeOptionWrites() const {
    return type_option_writes_;
  }
  const CovergroupInstance* AnyOf(const CovergroupDecl* decl) const;

 private:
  std::unordered_map<std::string, CovergroupInstance> instances_;
  std::unordered_map<uint64_t, CovergroupInstance*> held_;
  std::unordered_map<const CovergroupInstance*, uint64_t> identities_;
  std::unordered_map<const Variable*, const CovergroupDecl*> declared_;
  struct BuiltInstance {
    const CovergroupDecl* decl;
    const ClassTypeInfo* declaring_class;
    const CoverGroup* group;
  };
  std::vector<BuiltInstance> built_;
  std::vector<std::pair<std::string, CovergroupInstance*>> block_watchers_;
  std::unordered_map<
      const ClassTypeInfo*,
      std::vector<std::pair<std::string_view, const CovergroupDecl*>>>
      embedded_;
  ComposedCovergroups composed_;
  std::vector<TypeOptionWrite> type_option_writes_;
};

struct CovergroupSite {
  std::string key;
  const CovergroupDecl* decl = nullptr;
  ClassObject* owner = nullptr;
  const GenBlockConsts* gen_consts = nullptr;
};

CovergroupInstance* BuildCovergroupInstance(const CovergroupSite& site,
                                            const Expr* new_call,
                                            SimContext& ctx, Arena& arena);

void CreateCovergroupForVar(std::string_view name, const RtlirVariable& var,
                            Variable* v, SimContext& ctx, Arena& arena);

const CovergroupDecl* CovergroupOfType(const DataType& type, SimContext& ctx);

bool TryCreateCovergroupLocal(const DataType& type, const Expr* init,
                              Variable* v, SimContext& ctx, Arena& arena);

bool TryCovergroupNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

void RegisterUnitCovergroups(const std::vector<ModuleItem*>& items,
                             std::string_view scope, SimContext& ctx);

std::optional<Logic4Vec> CovergroupPropertyNew(const ClassTypeInfo* type,
                                               std::string_view name,
                                               const Expr* init,
                                               SimContext& ctx, Arena& arena);

bool TryCovergroupOptionAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

void SampleAtBlockEvent(std::string_view scope, bool is_begin, SimContext& ctx,
                        Arena& arena);

bool TryEvalCovergroupMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

bool TryEvalCovergroupMethodOnHandle(const Logic4Vec& handle, const Expr* expr,
                                     SimContext& ctx, Arena& arena,
                                     Logic4Vec& out);

bool TryEvalCovergroupOptionRead(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta

#endif
