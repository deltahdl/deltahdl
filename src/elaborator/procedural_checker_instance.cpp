#include "elaborator/procedural_checker_instance.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/checker_instance_binding.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §12.7.1 and §12.7.3: the variables the loop `s` declares for its body, a
// foreach loop's loop variables and each control variable a for loop's
// initialization gives a data type.
void AppendLoopLocals(const Stmt& s, std::vector<std::string_view>& locals) {
  locals.insert(locals.end(), s.foreach_vars.begin(), s.foreach_vars.end());
  for (size_t i = 0; i < s.for_inits.size() && i < s.for_init_types.size();
       ++i) {
    const Expr* var = s.for_inits[i]->lhs;
    if (s.for_init_types[i].kind != DataTypeKind::kImplicit && var != nullptr &&
        var->kind == ExprKind::kIdentifier) {
      locals.push_back(var->text);
    }
  }
}

// §17.3: no checker instance may stand inside a fork-join, fork-join_any or
// fork-join_none block, so one a fork statement encloses, `in_fork`, is
// reported and left out. `locals` are the variables the enclosing blocks
// and loops declare before `s`.
void CollectCheckerInstantiations(
    Stmt* s, bool in_fork, std::vector<std::string_view> locals,
    std::vector<CheckerInstantiationInProcedure>& out, DiagEngine& diag) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kCheckerInstantiation && in_fork) {
    diag.Error(s->range.start,
               "a checker instance cannot stand inside a fork-join, "
               "fork-join_any or fork-join_none block",
               Subclause("17.3"));
  } else if (s->kind == StmtKind::kCheckerInstantiation) {
    out.push_back({s, locals});
  }
  bool sub_in_fork = in_fork || s->kind == StmtKind::kFork;
  AppendLoopLocals(*s, locals);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectCheckerInstantiations(sub, sub_in_fork, locals, out, diag);
    // A block's variable declaration is visible to the statements after it.
    if (sub != nullptr && sub->kind == StmtKind::kVarDecl) {
      locals.push_back(sub->var_name);
    }
  });
}

}  // namespace

std::vector<CheckerInstantiationInProcedure> CheckerInstantiationsIn(
    Stmt* body, DiagEngine& diag) {
  std::vector<CheckerInstantiationInProcedure> out;
  CollectCheckerInstantiations(body, false, {}, out, diag);
  return out;
}

bool AdmitProceduralCheckerInstance(const ModuleItem* item,
                                    const ModuleDecl* child,
                                    const RtlirModule* mod, DiagEngine& diag) {
  if (child == nullptr) return true;
  if (child->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("'{}' is not a checker, and only a checker may be "
                           "instantiated in procedural code",
                           item->inst_module),
               Subclause("17.3"));
    return false;
  }
  if (mod->is_checker) {
    diag.Error(item->loc,
               std::format("checker '{}' cannot be instantiated in procedural "
                           "code that belongs to another checker",
                           item->inst_module),
               Subclause("17.3"));
    return false;
  }
  CheckCheckerInstForm(item, child, diag);
  return true;
}

}  // namespace delta
