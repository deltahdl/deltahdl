#include "simulation/compiled_sim.h"

#include <cstdint>
#include <utility>

#include "parser/ast.h"

namespace delta {

// =============================================================================
// CompiledProcess
// =============================================================================

CompiledProcess::CompiledProcess(uint32_t id, CompiledFn fn)
    : id_(id), fn_(std::move(fn)) {}

void CompiledProcess::Execute(SimContext& ctx) const {
  if (fn_) fn_(ctx);
}

// =============================================================================
// ProcessCompiler
// =============================================================================

bool ProcessCompiler::IsCompilable(const Stmt* body) {
  if (body == nullptr) return false;
  return !HasTimingControl(body);
}

CompiledProcess ProcessCompiler::Compile(uint32_t id, const Stmt* body) {
  if (!IsCompilable(body)) {
    return CompiledProcess(id, nullptr);
  }
  // Stub: return a valid but no-op compiled process.
  // Full code generation would translate the AST to direct C++ calls.
  return CompiledProcess(id, [](SimContext& /*ctx*/) {});
}

bool ProcessCompiler::HasTimingControl(const Stmt* stmt) {
  if (stmt == nullptr) return false;

  switch (stmt->kind) {
    case StmtKind::kTimingControl:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
      return true;
    case StmtKind::kBlock:
      return HasTimingControlInBlock(stmt->stmts);
    case StmtKind::kIf:
      return HasTimingControl(stmt->then_branch) ||
             HasTimingControl(stmt->else_branch);
    case StmtKind::kFor:
      return HasTimingControl(stmt->for_body);
    case StmtKind::kWhile:
    case StmtKind::kDoWhile:
    case StmtKind::kForever:
    case StmtKind::kRepeat:
      return HasTimingControl(stmt->body);
    case StmtKind::kFork:
      return HasTimingControlInBlock(stmt->fork_stmts);
    default:
      return false;
  }
}

bool ProcessCompiler::HasTimingControlInBlock(const std::vector<Stmt*>& stmts) {
  for (const auto* s : stmts) {
    if (HasTimingControl(s)) return true;
  }
  return false;
}

}  // namespace delta
