#include "elaborator/sdf_annotate_calls.h"

#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/assertion_walk.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool StmtCallsSdfAnnotate(const Stmt* stmt) {
  bool calls = false;
  ForEachStmtReadExpr(stmt, [&calls](const Expr* e) {
    calls = calls || AnySubExpr(e, [](const Expr* sub) {
              return sub->kind == ExprKind::kSystemCall &&
                     sub->callee == "$sdf_annotate";
            });
  });
  return calls;
}

static bool ModuleCallsSdfAnnotate(const RtlirModule& mod) {
  for (const RtlirProcess& proc : mod.processes) {
    if (StmtCallsSdfAnnotate(proc.body)) return true;
  }
  for (const ModuleItem* decl : mod.function_decls) {
    for (const Stmt* stmt : decl->func_body_stmts) {
      if (StmtCallsSdfAnnotate(stmt)) return true;
    }
  }
  return false;
}

bool DesignCallsSdfAnnotate(const RtlirDesign& design) {
  for (const auto& [name, mod] : design.all_modules) {
    if (ModuleCallsSdfAnnotate(*mod)) return true;
  }
  return false;
}

void WarnUwireNotMerged(DiagEngine& diag, SourceLoc loc, std::string_view port,
                        std::string_view inst) {
  diag.Warning(loc,
               std::format("uwire net on port '{}' of instance '{}' is not "
                           "merged into a single net",
                           port, inst),
               Subclause("23.3.3.6"));
}

void WarnUwireNetsKeptApart(const RtlirDesign& design, DiagEngine& diag) {
  if (!DesignCallsSdfAnnotate(design)) return;
  for (const auto& [name, mod] : design.all_modules) {
    for (const RtlirModuleInst& inst : mod->children) {
      for (const RtlirPortBinding& binding : inst.port_bindings) {
        if (!binding.uwire_net_join || binding.direction != Direction::kInout) {
          continue;
        }
        WarnUwireNotMerged(diag, binding.connection->loc, binding.port_name,
                           inst.inst_name);
      }
    }
  }
}

}  // namespace delta
