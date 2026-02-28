#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

class Arena;
class SimContext;

// =============================================================================
// SvCallable: represents a SystemVerilog task or function declaration
// =============================================================================

struct CallableParam {
  std::string_view name;
  Direction direction = Direction::kInput;
  uint32_t width = 1;
};

class SvCallable {
 public:
  SvCallable(std::string_view name, bool is_task,
             std::vector<CallableParam> params, Stmt* body);

  std::string_view Name() const { return name_; }
  bool IsTask() const { return is_task_; }
  const std::vector<CallableParam>& Params() const { return params_; }
  Stmt* Body() const { return body_; }

 private:
  std::string_view name_;
  bool is_task_;
  std::vector<CallableParam> params_;
  Stmt* body_;
};

// =============================================================================
// CallFrame: local state for a single task/function invocation
// =============================================================================

struct CallFrame {
  std::string_view callable_name;
  std::vector<Logic4Vec> locals;
  Logic4Vec return_value{};
  uint32_t caller_id = 0;
};

// =============================================================================
// SvCallableContext: manages a call stack of active invocations
// =============================================================================

class SvCallableContext {
 public:
  void PushFrame(const CallFrame& frame);
  void PopFrame();
  CallFrame* CurrentFrame();
  const CallFrame* CurrentFrame() const;
  uint32_t Depth() const { return static_cast<uint32_t>(stack_.size()); }
  bool Empty() const { return stack_.empty(); }

 private:
  std::vector<CallFrame> stack_;
};

}  // namespace delta
