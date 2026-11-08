#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

static void CollectElementSuffixes(const ArrayInfo& info, size_t dim,
                                   const std::string& prefix,
                                   std::vector<std::string>& out) {
  bool multi = !info.dim_sizes.empty();
  size_t dims = multi ? info.dim_sizes.size() : 1;
  if (dim == dims) {
    out.push_back(prefix);
    return;
  }
  uint32_t lo = multi ? info.dim_los[dim] : info.lo;
  uint32_t size = multi ? info.dim_sizes[dim] : info.size;
  for (uint32_t i = 0; i < size; ++i) {
    CollectElementSuffixes(info, dim + 1,
                           prefix + "[" + std::to_string(lo + i) + "]", out);
  }
}

static void AliasArray(std::string_view key, std::string_view qname,
                       SimContext& ctx, Arena& arena) {
  const ArrayInfo* found = ctx.FindArrayInfo(qname);
  if (found == nullptr) return;
  ArrayInfo info = *found;
  ctx.RegisterArray(key, info);
  if (info.is_dynamic) return;
  std::vector<std::string> suffixes;
  CollectElementSuffixes(info, 0, "", suffixes);
  for (const std::string& suffix : suffixes) {
    auto* elem_key = arena.Create<std::string>(std::string(key) + suffix);
    ctx.AliasVariable(*elem_key, std::string(qname) + suffix);
  }
}

static void AliasLayout(std::string_view key, std::string_view qname,
                        SimContext& ctx, Arena& arena) {
  const StructTypeInfo* found = ctx.GetVariableStructType(qname);
  if (found == nullptr) return;
  std::string_view stored = found->type_name;
  if (stored != qname) {
    StructTypeInfo own = *found;
    stored = *arena.Create<std::string>(std::string(qname));
    own.type_name = stored;
    ctx.RegisterStructType(stored, own);
    ctx.SetVariableStructType(stored, stored);
  }
  ctx.SetVariableStructType(key, stored);
}

void AliasVariableKinds(std::string_view key, std::string_view qname,
                        SimContext& ctx, Arena& arena) {
  std::string_view cls = ctx.GetVariableClassType(qname);
  if (!cls.empty()) ctx.SetVariableClassType(key, cls);
  if (ctx.IsRealVariable(qname)) ctx.RegisterRealVariable(key);
  if (const EnumTypeInfo* info = ctx.GetVariableEnumType(qname))
    ctx.SetVariableEnumType(key, info->type_name);
  ctx.AliasQueue(key, qname);
  ctx.AliasAssocArray(key, qname);
  AliasArray(key, qname, ctx, arena);
  AliasLayout(key, qname, ctx, arena);
  ctx.AliasSemaphore(key, qname);
  ctx.AliasMailbox(key, qname);
}

}  // namespace delta
