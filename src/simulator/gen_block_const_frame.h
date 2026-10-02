#pragma once

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// §27.4: binds each of `consts`, the implicit localparam of a loop generate
// block, as a signed 32-bit local of the innermost frame.
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

// §27.4: the implicit localparam of each loop generate block enclosing a
// declaration, "an integer parameter that has the same name and type as the
// loop index" whose value in each instance is the index that instance was
// elaborated with, bound in a frame of its own while the declaration's
// initializer is evaluated, as a process of the block has it
// (Lowerer::InstallGenBlockConsts). Read without it, `logic [7:0] e = i + 20`
// and `semaphore s = new(i + 1)` took the first instance's index in every
// instance. No frame for a declaration outside any loop generate block.
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
