#include "elaborator/gen_block_members.h"

#include <cstddef>
#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"

namespace delta {

DeclarationCounts CountDeclarations(const RtlirModule* mod) {
  return {mod->variables.size(), mod->nets.size(), mod->params.size(),
          mod->clocking_blocks.size()};
}

void RecordBlockItemMembers(RtlirModule* mod,
                            const GenBlockInstanceScope& scope,
                            const DeclarationCounts& before) {
  auto record_storage = [&](std::string_view stored) {
    if (!stored.starts_with(scope.prefix)) return;
    RecordGenBlockMember(mod->gen_block_members, scope.path,
                         {.kind = RtlirGenBlockMember::Kind::kStorage,
                          .name = stored.substr(scope.prefix.size()),
                          .storage = stored,
                          .param_index = 0,
                          .index_value = 0,
                          .gen_block_path = {}});
  };
  for (size_t i = before.variables; i < mod->variables.size(); ++i)
    record_storage(mod->variables[i].name);
  for (size_t i = before.nets; i < mod->nets.size(); ++i)
    record_storage(mod->nets[i].name);
  for (size_t i = before.params; i < mod->params.size(); ++i) {
    RecordGenBlockMember(mod->gen_block_members, scope.path,
                         {.kind = RtlirGenBlockMember::Kind::kParam,
                          .name = mod->params[i].name,
                          .storage = {},
                          .param_index = i,
                          .index_value = 0,
                          .gen_block_path = {}});
  }
  if (scope.prefixes.empty()) return;
  for (size_t i = before.clocking_blocks; i < mod->clocking_blocks.size();
       ++i) {
    mod->gen_block_clocking.push_back({.index = i,
                                       .block = mod->clocking_blocks[i],
                                       .gen_block_path = scope.path,
                                       .gen_block_prefixes = scope.prefixes});
  }
}

void EnterLoopBlockInstance(RtlirModule* mod, HierPath& path,
                            std::string_view genvar_name, int64_t index) {
  path.back().index = index;
  path.back().genvar = genvar_name;
  mod->gen_block_instances.push_back(path);
  RecordGenBlockMember(mod->gen_block_members, path,
                       {.kind = RtlirGenBlockMember::Kind::kIndex,
                        .name = genvar_name,
                        .storage = {},
                        .param_index = 0,
                        .index_value = index,
                        .gen_block_path = {}});
}

}  // namespace delta
