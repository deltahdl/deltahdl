#include "simulation/sv_callable.h"

#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast.h"

namespace delta {

// =============================================================================
// SvCallable
// =============================================================================

SvCallable::SvCallable(std::string_view name, bool is_task,
                       std::vector<CallableParam> params, Stmt* body)
    : name_(name), is_task_(is_task), params_(std::move(params)), body_(body) {}

// =============================================================================
// SvCallableContext
// =============================================================================

void SvCallableContext::PushFrame(const CallFrame& frame) {
  stack_.push_back(frame);
}

void SvCallableContext::PopFrame() {
  if (!stack_.empty()) {
    stack_.pop_back();
  }
}

CallFrame* SvCallableContext::CurrentFrame() {
  if (stack_.empty()) return nullptr;
  return &stack_.back();
}

const CallFrame* SvCallableContext::CurrentFrame() const {
  if (stack_.empty()) return nullptr;
  return &stack_.back();
}

}  // namespace delta
