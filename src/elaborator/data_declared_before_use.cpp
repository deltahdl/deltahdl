#include "elaborator/data_declared_before_use.h"

#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/unit_scope_order.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

namespace {

// Where one scope first declares each name it declares as data.
using Declarations = std::unordered_map<std::string_view, SourceLoc>;

bool DeclaresData(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kVarDecl ||
         item.kind == ModuleItemKind::kNetDecl ||
         item.kind == ModuleItemKind::kParamDecl;
}

Declarations DataDeclarationsOf(const std::vector<ModuleItem*>& items) {
  Declarations found;
  for (const ModuleItem* item : items)
    if (DeclaresData(*item)) found.emplace(item->name, item->loc);
  return found;
}

// The name at the root of a procedural target: of each select, member access
// and element of a concatenation written there.
void CollectTargetRoots(const Expr* e, std::vector<const Expr*>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    if (e->scope_prefix.empty()) out.push_back(e);
  } else if (e->kind == ExprKind::kSelect) {
    CollectTargetRoots(e->base, out);
  } else if (e->kind == ExprKind::kMemberAccess) {
    CollectTargetRoots(e->lhs, out);
  } else if (e->kind == ExprKind::kConcatenation) {
    for (const Expr* element : e->elements) CollectTargetRoots(element, out);
  }
}

bool NamesATarget(StmtKind kind) {
  switch (kind) {
    case StmtKind::kBlockingAssign:
    case StmtKind::kNonblockingAssign:
    case StmtKind::kAssign:
    case StmtKind::kDeassign:
    case StmtKind::kForce:
    case StmtKind::kRelease:
      return true;
    default:
      return false;
  }
}

// The data a statement and the statements under it write, passing by the
// names `locals` holds, which the statements declare themselves.
void CollectTargets(const Stmt* s,
                    const std::unordered_set<std::string_view>& locals,
                    std::vector<const Expr*>& out) {
  if (s == nullptr) return;
  if (NamesATarget(s->kind)) {
    std::vector<const Expr*> roots;
    CollectTargetRoots(s->lhs, roots);
    for (const Expr* root : roots)
      if (locals.count(root->text) == 0) out.push_back(root);
  }
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CollectTargets(sub, locals, out); });
}

// The reads an item makes outside any statement: a data declaration's value,
// a declaration's dimensions, a continuous assignment's expression, and a
// generate construct's condition and case item expressions.
void CollectItemReads(const ModuleItem& item, std::vector<const Expr*>& out) {
  if (item.kind == ModuleItemKind::kContAssign)
    CollectBareIdents(item.assign_rhs, out);
  else if (DeclaresData(item))
    CollectBareIdents(item.init_expr, out);
  for (const Expr* e : {item.gen_cond, item.data_type.packed_dim_left,
                        item.data_type.packed_dim_right})
    CollectBareIdents(e, out);
  for (const auto& [left, right] : item.data_type.extra_packed_dims) {
    CollectBareIdents(left, out);
    CollectBareIdents(right, out);
  }
  for (const Expr* dim : item.unpacked_dims) CollectBareIdents(dim, out);
  for (const auto& case_item : item.gen_case_items)
    for (const Expr* pattern : case_item.patterns)
      CollectBareIdents(pattern, out);
}

// The reads and writes of a procedure's or a subroutine's statements, passing
// by the formals `locals` starts with and the names the statements declare.
void CollectBodyUses(const std::vector<Stmt*>& body,
                     std::unordered_set<std::string_view> locals,
                     std::vector<const Expr*>& out) {
  for (const Stmt* s : body) CollectProcLocalNames(s, locals);
  for (const Stmt* s : body) {
    CollectProcRhsIdents(s, locals, out);
    CollectTargets(s, locals, out);
  }
}

// The uses a task's or function's body makes, passing by the names
// CollectSubroutineLocalNames finds it declares: its formals, a function's own
// name, and the declarations of its body.
void CollectSubroutineUses(const ModuleItem& subroutine,
                           std::vector<const Expr*>& out) {
  std::unordered_set<std::string_view> locals;
  CollectSubroutineLocalNames(&subroutine, locals);
  CollectBodyUses(subroutine.func_body_stmts, std::move(locals), out);
}

class UseBeforeDeclaration {
 public:
  UseBeforeDeclaration(const CompilationUnit& unit, const OuterScopes& outer,
                       DiagEngine& diag)
      : unit_(unit), outer_(outer), diag_(diag) {}

  void Scope(const std::vector<ModuleItem*>& items) {
    scopes_.push_back(DataDeclarationsOf(items));
    for (const ModuleItem* item : items) Item(*item);
    scopes_.pop_back();
  }

  // A class's properties are its data, read and written by its methods and
  // by the other properties' initializers. A name a base class may declare is
  // passed by, since the use may read the member the class inherits.
  void ClassBody(const ClassDecl& cls) {
    Declarations properties;
    std::vector<const Expr*> uses;
    for (const ClassMember* member : cls.members) {
      if (member->kind == ClassMemberKind::kProperty) {
        properties.emplace(member->name, member->loc);
        CollectBareIdents(member->init_expr, uses);
      }
      if (member->kind == ClassMemberKind::kMethod)
        CollectSubroutineUses(*member->method, uses);
      if (member->kind == ClassMemberKind::kClassDecl)
        ClassBody(*member->nested_class);
    }
    scopes_.push_back(std::move(properties));
    for (const Expr* use : uses)
      if (!MayInherit(cls, use->text)) Use(*use);
    scopes_.pop_back();
  }

 private:
  void Item(const ModuleItem& item) {
    std::vector<const Expr*> uses;
    CollectItemReads(item, uses);
    if (IsProceduralItemKind(item.kind)) CollectBodyUses({item.body}, {}, uses);
    if (item.kind == ModuleItemKind::kTaskDecl ||
        item.kind == ModuleItemKind::kFunctionDecl)
      CollectSubroutineUses(item, uses);
    for (const Expr* use : uses) Use(*use);
    if (item.kind == ModuleItemKind::kClassDecl) ClassBody(*item.class_decl);
    Scope(item.gen_body);
    if (item.gen_else != nullptr) Item(*item.gen_else);
    for (const auto& case_item : item.gen_case_items) Scope(case_item.body);
  }

  // Whether a class `cls` extends may declare a property `name`: one of its
  // bases does, or a base is found nowhere in the unit, so what it declares is
  // not known here. Elaborator::RunPreElaborationValidations has already
  // dropped the extends clause closing any cycle, so the walk ends.
  bool MayInherit(const ClassDecl& cls, std::string_view name) const {
    for (const ClassDecl* derived = &cls; !derived->base_class.empty();) {
      const ClassDecl* base = FindBaseClass(derived, &unit_);
      if (base == nullptr) return true;
      if (std::ranges::any_of(base->members, [&](const ClassMember* member) {
            return member->kind == ClassMemberKind::kProperty &&
                   member->name == name;
          }))
        return true;
      derived = base;
    }
    return false;
  }

  // A use stands above its declaration when every scope declaring the name
  // declares it only below the use, and no enclosing scope supplies it. A
  // module is walked once for each of its instances, so the report is made
  // once.
  void Use(const Expr& use) {
    bool declared = false;
    for (const Declarations& scope : scopes_) {
      auto it = scope.find(use.text);
      if (it == scope.end()) continue;
      if (!PrecedesInText(use.range.start, it->second)) return;
      declared = true;
    }
    if (!declared || outer_(use.text, use.range.start)) return;
    diag_.ErrorOnce(
        use.range.start,
        std::format("'{}' is used before its declaration", use.text),
        Subclause("6.5"));
  }

  const CompilationUnit& unit_;
  const OuterScopes& outer_;
  DiagEngine& diag_;
  std::vector<Declarations> scopes_;
};

}  // namespace

void ReportDataUsedAboveItsDeclaration(const std::vector<ModuleItem*>& items,
                                       const CompilationUnit& unit,
                                       const OuterScopes& outer,
                                       DiagEngine& diag) {
  UseBeforeDeclaration(unit, outer, diag).Scope(items);
}

// Whether the compilation unit declares `name` above `use`, where a scope it
// encloses reaches that declaration before one of its own further down.
static bool UnitNamesAbove(const CompilationUnit& unit, std::string_view name,
                           SourceLoc use) {
  return std::ranges::any_of(unit.cu_items, [&](const ModuleItem* item) {
    return item->name == name && PrecedesInText(item->loc, use);
  });
}

// Whether an import among `items` may make `name` visible: one naming it, or a
// wildcard import, which may.
static bool ImportReaches(const std::vector<ModuleItem*>& items,
                          std::string_view name) {
  return std::ranges::any_of(items, [&](const ModuleItem* item) {
    return item->kind == ModuleItemKind::kImportDecl &&
           (item->import_item.is_wildcard ||
            item->import_item.item_name == name);
  });
}

void ReportDataUsedAboveItsDeclaration(const CompilationUnit& unit,
                                       DiagEngine& diag) {
  for (const PackageDecl* pkg : unit.packages) {
    ReportDataUsedAboveItsDeclaration(
        pkg->items, unit,
        [&](std::string_view n, SourceLoc) {
          return ImportReaches(pkg->items, n);
        },
        diag);
  }
  const OuterScopes kUnitScope = [&](std::string_view n, SourceLoc use) {
    return ImportReaches(unit.cu_items, n) || UnitNamesAbove(unit, n, use);
  };
  ReportDataUsedAboveItsDeclaration(unit.cu_items, unit, kUnitScope, diag);
  UseBeforeDeclaration classes(unit, kUnitScope, diag);
  for (const ClassDecl* cls : unit.classes) classes.ClassBody(*cls);
}

bool NamedOutsideTheElement(const ModuleDecl* decl, const CompilationUnit* unit,
                            std::string_view name, SourceLoc use) {
  return std::ranges::any_of(
             decl->ports, [&](const PortDecl& p) { return p.name == name; }) ||
         UnitNamesAbove(*unit, name, use);
}

}  // namespace delta
