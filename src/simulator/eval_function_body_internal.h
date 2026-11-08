#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast_stmt.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

struct FuncExecCtx {
  Variable* ret_var;
  std::string_view func_name;
  std::string_view static_frame;
  SimContext& ctx;
  Arena& arena;
  uint32_t ret_width;
  bool is_static_sub = false;
  std::vector<std::string_view>* named_scopes = nullptr;
  bool array_return = false;
};

enum class FuncFlow : uint8_t { kNext, kBreak, kContinue, kReturn, kDisable };

FuncFlow ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec);

FuncFlow ExecFuncForeach(const Stmt* stmt, const FuncExecCtx& exec);

inline bool LoopGoesOn(FuncFlow flow) {
  return flow == FuncFlow::kNext || flow == FuncFlow::kContinue;
}

inline FuncFlow LoopExitFlow(FuncFlow last) {
  if (last == FuncFlow::kReturn || last == FuncFlow::kDisable) return last;
  return FuncFlow::kNext;
}

class FuncNamedScope {
 public:
  FuncNamedScope(std::string_view label, const FuncExecCtx& exec)
      : label_(label), exec_(exec) {
    if (label_.empty()) return;
    exec_.named_scopes->push_back(label_);
    exec_.ctx.PushActiveNamedScope(label_);
  }
  ~FuncNamedScope() {
    if (label_.empty()) return;
    exec_.ctx.PopActiveNamedScope();
    exec_.named_scopes->pop_back();
  }
  FuncNamedScope(const FuncNamedScope&) = delete;
  FuncNamedScope& operator=(const FuncNamedScope&) = delete;

  FuncFlow Leave(FuncFlow flow) const {
    if (flow != FuncFlow::kDisable || label_.empty() ||
        exec_.ctx.GetDisableTarget() != label_) {
      return flow;
    }
    exec_.ctx.ClearDisableTarget();
    return FuncFlow::kNext;
  }

 private:
  std::string_view label_;
  const FuncExecCtx& exec_;
};

}  // namespace delta
