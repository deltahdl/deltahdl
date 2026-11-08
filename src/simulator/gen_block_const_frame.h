#pragma once

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

inline void BindGenBlockConstVars(const GenBlockConsts& consts, SimContext& ctx,
                                  Arena& arena) {
  for (const auto& [name, value] : consts) {
    auto* var = arena.Create<Variable>();
    var->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(value));
    var->value.is_signed = true;
    var->is_signed = true;
    ctx.BindLocalVariable(name, var);
  }
}

class GenBlockConstFrame {
 public:
  GenBlockConstFrame(const GenBlockConsts& consts, SimContext& ctx,
                     Arena& arena)
      : ctx_(ctx), pushed_(!consts.empty()) {
    if (!pushed_) return;
    ctx_.PushScope();
    BindGenBlockConstVars(consts, ctx_, arena);
  }
  ~GenBlockConstFrame() {
    if (pushed_) ctx_.PopScope();
  }
  GenBlockConstFrame(const GenBlockConstFrame&) = delete;
  GenBlockConstFrame& operator=(const GenBlockConstFrame&) = delete;
  GenBlockConstFrame(GenBlockConstFrame&&) = delete;
  GenBlockConstFrame& operator=(GenBlockConstFrame&&) = delete;

 private:
  SimContext& ctx_;
  bool pushed_;
};

}  // namespace delta
