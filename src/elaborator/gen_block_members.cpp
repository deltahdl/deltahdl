// §27.4 and §27.5 with §23.6: what a generate block instance declares, listed
// with the path that names the instance, for the run to reach through it.

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

// The instance's variables and nets are stored under its prefix and its
// parameters under their simple names; a declaration stored under no such key
// belongs to no member and is left out. A clocking block is registered by the
// run rather than stored here, so it is listed with the prefixes a bare name
// in it resolves through (§23.9) and the path that names it from outside.
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
  RecordGenBlockMember(mod->gen_block_members, path,
                       {.kind = RtlirGenBlockMember::Kind::kIndex,
                        .name = genvar_name,
                        .storage = {},
                        .param_index = 0,
                        .index_value = index,
                        .gen_block_path = {}});
}

}  // namespace delta
