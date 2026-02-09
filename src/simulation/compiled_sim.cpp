#include "simulation/compiled_sim.h"

#include <cstdint>
#include <utility>

#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

using CompiledFn = CompiledProcess::CompiledFn;

static CompiledFn CompileStmt(const Stmt* stmt);

static CompiledFn CompileBlock(const Stmt* stmt) {
  std::vector<CompiledFn> steps;
  for (auto* s : stmt->stmts) {
    auto fn = CompileStmt(s);
    if (fn) steps.push_back(std::move(fn));
  }
  return [fns = std::move(steps)](SimContext& ctx) {
    for (auto& fn : fns) {
      fn(ctx);
    }
  };
}

static CompiledFn CompileBlockingAssign(const Stmt* stmt) {
  return [stmt](SimContext& ctx) {
    auto& arena = ctx.GetArena();
    auto val = EvalExpr(stmt->rhs, ctx, arena);
    if (!stmt->lhs) return;
    auto* var = ctx.FindVariable(stmt->lhs->text);
    if (var) var->value = val;
  };
}

static CompiledFn CompileIf(const Stmt* stmt) {
  auto then_fn = stmt->then_branch ? CompileStmt(stmt->then_branch) : nullptr;
  auto else_fn = stmt->else_branch ? CompileStmt(stmt->else_branch) : nullptr;
  return [stmt, then_fn = std::move(then_fn),
          else_fn = std::move(else_fn)](SimContext& ctx) {
    auto cond = EvalExpr(stmt->condition, ctx, ctx.GetArena());
    if (cond.ToUint64() != 0) {
      if (then_fn) then_fn(ctx);
    } else {
      if (else_fn) else_fn(ctx);
    }
  };
}

static CompiledFn CompileExprStmt(const Stmt* stmt) {
  return [stmt](SimContext& ctx) { EvalExpr(stmt->expr, ctx, ctx.GetArena()); };
}

static CompiledFn CompileStmt(const Stmt* stmt) {
  if (!stmt) return nullptr;
  switch (stmt->kind) {
    case StmtKind::kBlock:
      return CompileBlock(stmt);
    case StmtKind::kBlockingAssign:
      return CompileBlockingAssign(stmt);
    case StmtKind::kIf:
      return CompileIf(stmt);
    case StmtKind::kExprStmt:
      return CompileExprStmt(stmt);
    default:
      return nullptr;
  }
}

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
  auto fn = CompileStmt(body);
  if (!fn) return CompiledProcess(id, nullptr);
  return CompiledProcess(id, std::move(fn));
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
