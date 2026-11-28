#include "elaborator/typedef_cycles.h"

#include <cstddef>
#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct TypedefScope {
  std::string_view package;
  std::vector<ModuleItem*> definitions;
  std::unordered_set<std::string_view> forward_names;
};

class TypedefCycles {
 public:
  explicit TypedefCycles(DiagEngine& diag) : diag_(diag) {}

  void Unit(const CompilationUnit& unit) {
    Scope(unit.cu_items, {});
    for (ClassDecl* cls : unit.classes) Class(*cls);
    for (PackageDecl* pkg : unit.packages) Scope(pkg->items, pkg->name);
    for (const std::vector<ModuleDecl*>* decls :
         {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
      for (ModuleDecl* decl : *decls) Scope(decl->items, {});
    }
  }

 private:
  void Scope(const std::vector<ModuleItem*>& items, std::string_view package) {
    TypedefScope scope{package, {}, {}};
    for (ModuleItem* item : items) Gather(item, scope);
    Break(scope);
    for (ModuleItem* item : items) Nested(*item);
  }

  static void Gather(ModuleItem* item, TypedefScope& scope) {
    if (item == nullptr || item->kind != ModuleItemKind::kTypedef ||
        item->data_type.kind == DataTypeKind::kVoid) {
      return;
    }
    if (item->typedef_type.kind == DataTypeKind::kImplicit) {
      scope.forward_names.insert(item->name);
      return;
    }
    scope.definitions.push_back(item);
  }

  void Nested(ModuleItem& item) {
    switch (item.kind) {
      case ModuleItemKind::kGenerateIf:
        for (ModuleItem* arm = &item; arm != nullptr; arm = arm->gen_else)
          Scope(arm->gen_body, {});
        break;
      case ModuleItemKind::kGenerateFor:
        Scope(item.gen_body, {});
        break;
      case ModuleItemKind::kGenerateCase:
        for (const GenerateCaseItem& choice : item.gen_case_items)
          Scope(choice.body, {});
        break;
      case ModuleItemKind::kFunctionDecl:
      case ModuleItemKind::kTaskDecl:
        Statements(item.func_body_stmts);
        break;
      case ModuleItemKind::kClassDecl:
        if (item.class_decl != nullptr) Class(*item.class_decl);
        break;
      default:
        if (item.body != nullptr) Statements({item.body});
        break;
    }
  }

  void Statements(const std::vector<Stmt*>& stmts) {
    TypedefScope scope{{}, {}, {}};
    for (Stmt* s : stmts) {
      if (s != nullptr && s->kind == StmtKind::kBlockItemDecl)
        Gather(s->decl_item, scope);
    }
    Break(scope);
    for (Stmt* s : stmts) NestedStatement(s);
  }

  void NestedStatement(Stmt* s) {
    if (s == nullptr) return;
    if (s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork) {
      std::vector<Stmt*> children;
      ForEachChildStmt(s, [&children](Stmt* sub) { children.push_back(sub); });
      Statements(children);
      return;
    }
    ForEachChildStmt(s, [this](Stmt* sub) { NestedStatement(sub); });
  }

  void Class(ClassDecl& cls) {
    TypedefScope scope{{}, {}, {}};
    for (ClassMember* member : cls.members) Gather(member->typedef_item, scope);
    Break(scope);
    for (ClassMember* member : cls.members) {
      if (member->method != nullptr) Nested(*member->method);
      if (member->nested_class != nullptr) Class(*member->nested_class);
    }
  }

  static const ModuleItem* Next(const ModuleItem& def,
                                const TypedefScope& scope) {
    const DataType& type = def.typedef_type;
    if (type.kind != DataTypeKind::kNamed || !type.type_params.empty() ||
        !type.outer_scope_names.empty()) {
      return nullptr;
    }
    if (!type.scope_name.empty() &&
        (scope.package.empty() || type.scope_name != scope.package)) {
      return nullptr;
    }
    const ModuleItem* next = nullptr;
    for (const ModuleItem* other : scope.definitions) {
      if (other->name == type.type_name) next = other;
    }
    return next;
  }

  static std::vector<const ModuleItem*> CycleThrough(
      const ModuleItem* def, const TypedefScope& scope) {
    std::vector<const ModuleItem*> path{def};
    for (const ModuleItem* at = Next(*def, scope); at != nullptr;
         at = Next(*at, scope)) {
      if (at == def) return path;
      if (path.size() > scope.definitions.size()) break;
      path.push_back(at);
    }
    return {};
  }

  static size_t PositionOf(const ModuleItem* item, const TypedefScope& scope) {
    size_t at = 0;
    while (scope.definitions[at] != item) ++at;
    return at;
  }

  static bool ClosesCycle(const std::vector<const ModuleItem*>& cycle,
                          const TypedefScope& scope) {
    const size_t kAt = PositionOf(cycle.front(), scope);
    for (const ModuleItem* member : cycle) {
      if (PositionOf(member, scope) > kAt) return false;
    }
    return true;
  }

  static bool HasForwardTypedef(const std::vector<const ModuleItem*>& cycle,
                                const TypedefScope& scope) {
    for (const ModuleItem* member : cycle) {
      if (scope.forward_names.count(member->name) != 0) return true;
    }
    return false;
  }

  void Report(const std::vector<const ModuleItem*>& cycle,
              const TypedefScope& scope) {
    const ModuleItem* closing = cycle.front();
    if (HasForwardTypedef(cycle, scope)) {
      diag_.Error(closing->loc,
                  std::format("typedef '{}' does not resolve to a data type",
                              closing->name),
                  Subclause("6.18"));
      return;
    }
    size_t earliest = 0;
    for (size_t i = 1; i < cycle.size(); ++i) {
      if (PositionOf(cycle[i], scope) < PositionOf(cycle[earliest], scope))
        earliest = i;
    }
    const ModuleItem* named = cycle[(earliest + 1) % cycle.size()];
    diag_.Error(cycle[earliest]->loc,
                std::format("declaration of type '{}' does not precede this "
                            "reference to it",
                            named->name),
                Subclause("6.18"));
  }

  void Break(const TypedefScope& scope) {
    std::vector<ModuleItem*> closing;
    for (ModuleItem* def : scope.definitions) {
      std::vector<const ModuleItem*> cycle = CycleThrough(def, scope);
      if (cycle.empty() || !ClosesCycle(cycle, scope)) continue;
      Report(cycle, scope);
      closing.push_back(def);
    }
    for (ModuleItem* def : closing) {
      DataType resolved;
      resolved.kind = DataTypeKind::kInt;
      resolved.is_signed = true;
      def->typedef_type = resolved;
    }
  }

  DiagEngine& diag_;
};

}  // namespace

void BreakTypedefCycles(const std::vector<CompilationUnit*>& units,
                        DiagEngine& diag) {
  TypedefCycles cycles(diag);
  for (const CompilationUnit* unit : units) cycles.Unit(*unit);
}

}  // namespace delta
