#include "elaborator/unpacked_dim_reads.h"

#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct DimReadScan {
  const std::unordered_map<std::string_view, DataTypeKind>& values;
  DiagEngine& diag;
};

// The names a block or a subroutine declares again, each hiding the module's
// variable or net of that name from what is declared after it.
using HiddenNames = std::unordered_set<std::string_view>;

}  // namespace

static bool ReadsNoValue(ExprKind kind) {
  return kind == ExprKind::kCall || kind == ExprKind::kSystemCall ||
         kind == ExprKind::kMemberAccess || kind == ExprKind::kTypeRef;
}

// Reports each of the module's variables and nets `e`, written in an unpacked
// dimension of `declared`, reads.
static void ReportValueReads(const Expr* e, std::string_view declared,
                             const HiddenNames& hidden,
                             const DimReadScan& scan) {
  if (e == nullptr || ReadsNoValue(e->kind)) return;
  if (e->kind == ExprKind::kIdentifier && scan.values.contains(e->text) &&
      !hidden.contains(e->text)) {
    scan.diag.Error(e->range.start,
                    std::format("unpacked dimension of '{}' reads '{}', which "
                                "is no constant, so the dimension is not a "
                                "constant expression",
                                declared, e->text),
                    Subclause("7.4.2"));
  }
  ForEachExprChild(e, [&](const Expr* child) {
    ReportValueReads(child, declared, hidden, scan);
  });
}

static void CheckDims(std::string_view declared, const std::vector<Expr*>& dims,
                      const HiddenNames& hidden, const DimReadScan& scan) {
  for (const Expr* dim : dims) ReportValueReads(dim, declared, hidden, scan);
}

// §6.21: a name a block declares is visible in that block and the blocks
// nested in it, so it hides the module's from the rest of the block alone.
static void CheckStmt(const Stmt* s, HiddenNames& hidden,
                      const DimReadScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kVarDecl) {
    CheckDims(s->var_name, s->var_unpacked_dims, hidden, scan);
    hidden.insert(s->var_name);
  }
  if (s->kind == StmtKind::kBlockItemDecl) hidden.insert(s->decl_item->name);
  if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) {
    HiddenNames inner = hidden;
    ForEachChildStmt(s, [&](Stmt* const& sub) { CheckStmt(sub, inner, scan); });
    return;
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) { CheckStmt(sub, hidden, scan); });
}

void CheckVariableReadsInUnpackedDims(
    const ModuleDecl* decl,
    const std::unordered_map<std::string_view, DataTypeKind>& values,
    DiagEngine& diag) {
  const DimReadScan kScan{values, diag};
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      CheckDims(item->name, item->unpacked_dims, {}, kScan);
    }
    // A subroutine's arguments are declared in its body's scope, and so is a
    // function's own name, the variable its result is written to (§13.4.1).
    HiddenNames hidden{item->name};
    for (const FunctionArg& arg : item->func_args) hidden.insert(arg.name);
    CheckStmt(item->body, hidden, kScan);
    for (const Stmt* s : item->func_body_stmts) CheckStmt(s, hidden, kScan);
  }
}

}  // namespace delta
