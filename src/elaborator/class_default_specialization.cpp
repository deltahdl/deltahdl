#include "elaborator/class_default_specialization.h"

#include <cstddef>
#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

std::string_view ParameterWithoutDefault(const ClassDecl& cls) {
  for (std::size_t i = 0; i < cls.params.size(); ++i) {
    const auto& [name, value] = cls.params[i];
    const bool kDefaulted =
        cls.type_param_names.contains(name)
            ? cls.param_types.at(i).kind != DataTypeKind::kImplicit
            : value != nullptr;
    if (!kDefaulted) return name;
  }
  return {};
}

namespace {

// Reports the declarations of one compilation unit that name a parameterized
// class without arguments where it has no default specialization.
class UnadornedUseWalk {
 public:
  UnadornedUseWalk(const CompilationUnit& unit, DiagEngine& diag)
      : unit_(unit), diag_(diag) {}

  // The type `type` written at `loc`, unless `local` holds its name: a type
  // parameter or typedef of the class the type is written in, which names no
  // class of the scope around it.
  void Type(const DataType& type, SourceLoc loc,
            const std::unordered_set<std::string_view>& local = {}) {
    if (type.kind != DataTypeKind::kNamed || !type.type_params.empty() ||
        !type.scope_name.empty() || local.contains(type.type_name)) {
      return;
    }
    Class(type.type_name, loc);
  }

  // The class named `name` used with no arguments at `loc`.
  void Class(std::string_view name, SourceLoc loc) {
    const ClassDecl* cls = FindClassDecl(name, &unit_);
    if (cls == nullptr) return;
    const std::string_view kMissing = ParameterWithoutDefault(*cls);
    if (kMissing.empty()) return;
    diag_.Error(loc,
                std::format("parameterized class '{}' has no default "
                            "specialization; parameter '{}' has no default "
                            "value",
                            cls->name, kMissing),
                Subclause("8.25"));
  }

  // A subroutine's return type, its arguments and the variables its body
  // declares.
  void Subroutine(const ModuleItem& sub,
                  const std::unordered_set<std::string_view>& local = {}) {
    Type(sub.return_type, sub.loc, local);
    for (const FunctionArg& arg : sub.func_args) {
      Type(arg.data_type, sub.loc, local);
    }
    for (const Stmt* s : sub.func_body_stmts) Statement(s, local);
  }

  // The variables `s` and the statements inside it declare.
  void Statement(const Stmt* s,
                 const std::unordered_set<std::string_view>& local = {}) {
    if (s == nullptr) return;
    if (s->kind == StmtKind::kVarDecl) {
      Type(s->var_decl_type, s->range.start, local);
    }
    ForEachChildStmt(s, [&](const Stmt* sub) { Statement(sub, local); });
  }

  // Every declaration among `items`, generate blocks included, but for the
  // variables `items` declares where `with_vars` is false.
  void Items(const std::vector<ModuleItem*>& items, bool with_vars) {
    for (const ModuleItem* item : items) Item(*item, with_vars);
  }

  // A class's base, properties, typedefs and methods.
  void ClassBody(const ClassDecl& cls) {
    if (!cls.base_class.empty() && cls.base_class_type_params.empty() &&
        cls.extends_args.empty() && !cls.extends_has_default) {
      Class(cls.base_class, cls.range.start);
    }
    std::unordered_set<std::string_view> local = cls.type_param_names;
    for (const ClassMember* m : cls.members) {
      if (m->typedef_item != nullptr) local.insert(m->name);
    }
    for (const ClassMember* m : cls.members) {
      if (m->method != nullptr) {
        Subroutine(*m->method, local);
      } else if (m->typedef_item != nullptr) {
        Type(m->typedef_item->typedef_type, m->loc, local);
      } else if (m->kind == ClassMemberKind::kProperty) {
        Type(m->data_type, m->loc, local);
      }
    }
  }

 private:
  void Item(const ModuleItem& item, bool with_vars) {
    if (item.kind == ModuleItemKind::kVarDecl && with_vars) {
      Type(item.data_type, item.loc);
    } else if (item.kind == ModuleItemKind::kTypedef) {
      Type(item.typedef_type, item.loc);
    } else if (item.kind == ModuleItemKind::kFunctionDecl ||
               item.kind == ModuleItemKind::kTaskDecl) {
      Subroutine(item);
    }
    Statement(item.body);
    Items(item.gen_body, with_vars);
    if (item.gen_else != nullptr) Item(*item.gen_else, with_vars);
    for (const GenerateCaseItem& arm : item.gen_case_items) {
      Items(arm.body, with_vars);
    }
  }

  const CompilationUnit& unit_;
  DiagEngine& diag_;
};

}  // namespace

void ReportUnadornedClassesWithoutDefaults(const CompilationUnit& unit,
                                           DiagEngine& diag) {
  UnadornedUseWalk walk(unit, diag);
  walk.Items(unit.cu_items, true);
  for (const auto* group :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *group) walk.Items(decl->items, false);
  }
  for (const PackageDecl* package : unit.packages) {
    walk.Items(package->items, true);
  }
  for (const ClassDecl* cls : AllClassDecls(&unit)) walk.ClassBody(*cls);
}

}  // namespace delta
