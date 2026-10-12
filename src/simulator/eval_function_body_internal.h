#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast_stmt.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

// What the statement executor for a subroutine body shares across the files
// that hold it: eval_function_body.cpp, which dispatches every statement form,
// and eval_function_body_foreach.cpp, which runs a foreach.

// The environment in which a subroutine body executes (§13.4): the return
// variable that a `return` writes, the subroutine name that variable is
// declared under, the key its static function-local variables are kept under
// (§13.4.2, StaticLocalFrame), and the simulation/evaluation context. These
// travel together through the entire recursive statement executor, so they
// are bundled into one entity rather than passed field by field.
struct FuncExecCtx {
  Variable* ret_var;
  std::string_view func_name;
  std::string_view static_frame;
  SimContext& ctx;
  Arena& arena;
  // The declared width of the return value, or zero where the return type has
  // no packed width -- void, a string, a class handle, a parameterized method's
  // type. ExecFuncReturn reads zero as "leave the expression's own vector
  // alone".
  uint32_t ret_width;
  // §13.4.2: whether the subroutine is static, so a local declared with no
  // lifetime is static storage kept between calls (ExecFuncVarDecl).
  bool is_static_sub = false;
  // §9.6.2: the labels of the named blocks and labeled loops the running
  // statement stands in, innermost last, which a `disable` in the body can end.
  std::vector<std::string_view>* named_scopes = nullptr;
  // §13.4.1: whether the implicit variable is an unpacked array
  // (ShapeArrayReturnVariable), which a `return` assigns rather than stores.
  bool array_return = false;
};

// Where control goes once a statement of the body has run (§12.8): on to
// the statement after it, out of the innermost enclosing loop (`break`), to
// the end of the innermost enclosing loop's body (`continue`), or out of the
// subroutine (`return`), or to the end of the named block or labeled loop a
// `disable` named (§9.6.2), which SimContext::GetDisableTarget holds. Every
// executor here answers one of these; a block, a conditional and a case hand
// up whatever the statement they ran answered, a loop consumes kBreak and
// kContinue and hands up kReturn, the block or loop a disable named consumes
// that kDisable, and ExecFunctionBody stops at anything but kNext. Before this
// the executors answered a bool meaning "a return ran", and a break or continue
// reached nothing that acted on it: uvm_report_server::reset_severity_counts, a
// `forever` over an enumeration that breaks at its last member, never ended.
enum class FuncFlow : uint8_t { kNext, kBreak, kContinue, kReturn, kDisable };

FuncFlow ExecFuncStmt(const Stmt* stmt, const FuncExecCtx& exec);

// §12.7.3: runs a foreach in a subroutine body. Defined in
// eval_function_body_foreach.cpp.
FuncFlow ExecFuncForeach(const Stmt* stmt, const FuncExecCtx& exec);

// §12.8: a loop goes on to its next iteration when its body ran to the end or
// reached a `continue`; a `break` or a `return` ends the iterating.
inline bool LoopGoesOn(FuncFlow flow) {
  return flow == FuncFlow::kNext || flow == FuncFlow::kContinue;
}

// What a loop answers once it has stopped iterating, given what its body
// answered last: a `return` leaves the subroutine and a `disable` of a scope
// around the loop leaves the loop too, so both pass through, and a `break`, a
// `continue` or a body that ran to the end is consumed by the loop, which is
// then followed by the statement after it.
inline FuncFlow LoopExitFlow(FuncFlow last) {
  if (last == FuncFlow::kReturn || last == FuncFlow::kDisable) return last;
  return FuncFlow::kNext;
}

// §9.6.2: the named block or labeled statement `label` enters, which a
// disable in it can end. Leave() answers what the scope hands on: a disable
// naming this scope ends here and control goes on after it.
class FuncNamedScope {
 public:
  FuncNamedScope(std::string_view label, const FuncExecCtx& exec)
      : label_(label), exec_(exec) {
    if (!label_.empty()) exec_.named_scopes->push_back(label_);
  }
  ~FuncNamedScope() {
    if (!label_.empty()) exec_.named_scopes->pop_back();
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
