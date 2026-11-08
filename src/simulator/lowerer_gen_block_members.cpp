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
        ctx_.AliasSemaphore(*key, *stored);
        ctx_.AliasMailbox(*key, *stored);
        break;
      }
      case RtlirGenBlockMember::Kind::kParam:
        LowerParam(*mod, mod->params[member.param_index], *key);
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
