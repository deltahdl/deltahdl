#include "elaborator/elaborator_defparam_block.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_defparam_walk.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

bool IsNamedBlock(const Stmt* s) {
  return !s->label.empty() &&
         (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork);
}

bool DeclaresParamNamed(const Stmt* s, std::string_view name) {
  return s->kind == StmtKind::kVarDecl && s->var_is_param &&
         s->var_name == name;
}

const Stmt* DeclaredParam(const Stmt* block, std::string_view name) {
  const Stmt* found = nullptr;
  ForEachChildStmt(block, [&](const Stmt* sub) {
    if (sub != nullptr && DeclaresParamNamed(sub, name)) found = sub;
  });
  return found;
}

const Stmt* FindUnder(const Stmt* s, const HierPath& blocks, std::size_t i,
                      std::string_view name) {
  if (s == nullptr) return nullptr;
  if (IsNamedBlock(s)) {
    if (blocks[i].has_index || s->label != blocks[i].name) return nullptr;
    if (i + 1 == blocks.size()) return DeclaredParam(s, name);
    ++i;
  }
  const Stmt* found = nullptr;
  ForEachChildStmt(s, [&](const Stmt* sub) {
    if (found == nullptr) found = FindUnder(sub, blocks, i, name);
  });
  return found;
}

const Stmt* FindInSubroutine(const ModuleItem& sub, const HierPath& blocks,
                             std::string_view name) {
  if (blocks.front().has_index || sub.name != blocks.front().name) {
    return nullptr;
  }
  for (const Stmt* s : sub.func_body_stmts) {
    if (blocks.size() > 1) {
      if (const Stmt* found = FindUnder(s, blocks, 1, name)) return found;
    } else if (DeclaresParamNamed(s, name)) {
      return s;
    }
  }
  return nullptr;
}

}  // namespace

const Stmt* FindBlockParamDecl(const RtlirModule& mod, const HierPath& blocks,
                               std::string_view name) {
  if (blocks.empty()) return nullptr;
  for (const auto& proc : mod.processes) {
    if (const Stmt* found = FindUnder(proc.body, blocks, 0, name)) {
      return found;
    }
  }
  for (const ModuleItem* sub : mod.function_decls) {
    if (const Stmt* found = FindInSubroutine(*sub, blocks, name)) return found;
  }
  return nullptr;
}

Expr* BlockParamInit(Expr* value, const ScopeMap& scope, Arena& arena) {
  if (value->kind == ExprKind::kIntegerLiteral ||
      value->kind == ExprKind::kRealLiteral ||
      value->kind == ExprKind::kStringLiteral) {
    return value;
  }
  std::optional<int64_t> folded = ConstEvalInt(value, scope);
  if (!folded) return nullptr;
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->int_val = *folded;
  return literal;
}

static void RecordBlockParamOverride(RtlirModule& mod, const Stmt* decl,
                                     Expr* init) {
  for (auto& recorded : mod.block_param_overrides) {
    if (recorded.decl == decl) {
      recorded.init = init;
      return;
    }
  }
  mod.block_param_overrides.push_back({decl, init});
}

bool ElaboratorData::ApplyBlockParamDefparam(RtlirModule* mod,
                                             const HierPath& writer,
                                             const HierPath& path,
                                             const BlockParamDefparam& d) {
  if (path.size() < 2) return false;
  ElementIsolator isolate = [&](RtlirModule& parent, RtlirModuleInst& elem) {
    IsolateArrayElement(parent, elem, d.arena);
  };
  std::vector<PathDescent> descents;
  DefparamPathEnd reach =
      WalkDefparamPath(mod, path, writer, descents, isolate);
  const Stmt* decl =
      FindBlockParamDecl(*reach.mod, reach.blocks, path.back().name);
  for (RtlirModule* top : defparam_top_roots_) {
    if (decl != nullptr || !writer.empty()) break;
    if (top->name != path.front().name) continue;
    HierPath steps(path.begin() + 1, path.end());
    if (EscapesWriterBlock(defparam_writer_blocks_, mod, top, steps)) break;
    reach = WalkDefparamPath(top, steps, {}, descents, isolate);
    decl = FindBlockParamDecl(*reach.mod, reach.blocks, steps.back().name);
  }
  if (decl == nullptr) return false;
  if (decl->decl_item->is_localparam) {
    d.diag.Error(d.loc, "defparam cannot override a local parameter",
                 Subclause("23.10.1"));
    return true;
  }
  Expr* init = BlockParamInit(d.value, d.scope, d.arena);
  if (init == nullptr) {
    d.diag.Warning(d.loc, "defparam value is not constant",
                   Subclause("23.10.1"));
    return true;
  }
  RecordBlockParamOverride(*reach.mod, decl, init);
  return true;
}

}  // namespace delta
