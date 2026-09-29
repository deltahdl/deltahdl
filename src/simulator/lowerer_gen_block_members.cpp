// §27.4 and §27.5 with §23.6: what a named generate block instance declares,
// registered under the hierarchical name that reaches it from outside the
// block, `g.v` or `u.g[1].v`, beside the flattened key the elaborator stores
// it under and a reference inside the block reads it by.

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// A variable or net is answered under the path as the object stored under its
// flattened key, shared rather than copied, so a write through either name is
// read through the other. A parameter is stored under its simple name, which
// every instance of a loop block shares, so each instance's is lowered afresh
// under the path, as is the loop index's implicit localparam (§27.4), an
// integer holding the index the instance was elaborated with.
void Lowerer::RegisterGenBlockMembers(const RtlirModule* mod) {
  for (const RtlirGenBlockMember& member : mod->gen_block_members) {
    auto* key = arena_.Create<std::string>(inst_prefix_ +
                                           GenBlockName(member.gen_block_path) +
                                           "." + std::string(member.name));
    switch (member.kind) {
      case RtlirGenBlockMember::Kind::kStorage: {
        auto* stored = arena_.Create<std::string>(inst_prefix_ +
                                                  std::string(member.storage));
        ctx_.AliasVariable(*key, *stored);
        AliasVariableKinds(*key, *stored, ctx_, arena_);
        ctx_.AliasNet(*key, *stored);
        break;
      }
      case RtlirGenBlockMember::Kind::kParam:
        LowerParam(mod->params[member.param_index], *key);
        break;
      case RtlirGenBlockMember::Kind::kIndex: {
        Variable* var = ctx_.CreateVariable(*key, 32);
        var->value = MakeLogic4VecVal(
            arena_, 32, static_cast<uint64_t>(member.index_value));
        var->is_signed = true;
        var->value.is_signed = true;
        break;
      }
    }
  }
}

}  // namespace delta
