#include "elaborator/instance_local_types.h"

#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct InstanceScan {
  const ModuleDecl* decl;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

}  // namespace

static const ModuleItem* FindItem(const ModuleDecl* mod, ModuleItemKind kind,
                                  std::string_view name) {
  for (const ModuleItem* item : mod->items) {
    if (item->kind == kind && item->name == name) return item;
  }
  return nullptr;
}

static bool DeclaresClass(const ModuleDecl* mod, std::string_view name) {
  for (const ModuleItem* item : mod->items) {
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl->name == name) {
      return true;
    }
  }
  return false;
}

// The module the instance `name` of the scanned module instantiates.
static const ModuleDecl* ModuleOfInstance(std::string_view name,
                                          const InstanceScan& scan) {
  for (const ModuleItem* item : scan.decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst || item->inst_name != name) {
      continue;
    }
    for (const ModuleDecl* mod : scan.unit->modules) {
      if (mod->name == item->inst_module) return mod;
    }
  }
  return nullptr;
}

// Whether `dtype`, written in `mod`, is a type `mod` declares, by a typedef,
// as a class or in place, of a kind no other type is equivalent to.
static bool IsOwnStrictType(const DataType& dtype, const ModuleDecl* mod) {
  const DataType* type = &dtype;
  if (dtype.kind == DataTypeKind::kNamed) {
    if (!dtype.scope_name.empty()) return false;
    const ModuleItem* td =
        FindItem(mod, ModuleItemKind::kTypedef, dtype.type_name);
    if (td == nullptr) return DeclaresClass(mod, dtype.type_name);
    type = &td->typedef_type;
  }
  if (type->kind == DataTypeKind::kEnum) return true;
  return (type->kind == DataTypeKind::kStruct ||
          type->kind == DataTypeKind::kUnion) &&
         !type->is_packed;
}

// The `inst.var` that `e` is, or null.
static const Expr* InstanceMember(const Expr* e) {
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution ||
      e->lhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return e;
}

static bool HasInstanceOwnStrictType(const Expr* access,
                                     const InstanceScan& scan) {
  const ModuleDecl* mod = ModuleOfInstance(access->lhs->text, scan);
  if (mod == nullptr) return false;
  const ModuleItem* var =
      FindItem(mod, ModuleItemKind::kVarDecl, access->rhs->text);
  return var != nullptr && IsOwnStrictType(var->data_type, mod);
}

static void CheckAssign(const Expr* lhs, const Expr* rhs, SourceLoc loc,
                        const InstanceScan& scan) {
  const Expr* target = InstanceMember(lhs);
  const Expr* value = InstanceMember(rhs);
  if (target == nullptr || value == nullptr ||
      target->lhs->text == value->lhs->text) {
    return;
  }
  if (!HasInstanceOwnStrictType(target, scan) ||
      !HasInstanceOwnStrictType(value, scan)) {
    return;
  }
  scan.diag.Error(
      loc,
      std::format("'{}.{}' and '{}.{}' have types the instances '{}' and '{}' "
                  "each declare for themselves, which are distinct types",
                  target->lhs->text, target->rhs->text, value->lhs->text,
                  value->rhs->text, target->lhs->text, value->lhs->text),
      Subclause("6.22"));
}

static void CheckStmt(const Stmt* s, const InstanceScan& scan) {
  if (s == nullptr) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckAssign(s->lhs, s->rhs, s->range.start, scan);
  }
  ForEachChildStmt(s, [&scan](Stmt* const& sub) { CheckStmt(sub, scan); });
}

void CheckInstanceLocalTypeAssignments(const ModuleDecl* decl,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  const InstanceScan kScan{decl, unit, diag};
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckAssign(item->assign_lhs, item->assign_rhs, item->loc, kScan);
    }
    CheckStmt(item->body, kScan);
  }
}

}  // namespace delta
