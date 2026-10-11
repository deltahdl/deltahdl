#include "elaborator/class_default_specialization.h"

#include <cstddef>
#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_map>
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
// class without arguments where it has no default specialization, or write a
// type behind its unadorned name where only a specialization may stand.
class UnadornedUseWalk {
 public:
  UnadornedUseWalk(const CompilationUnit& unit, DiagEngine& diag)
      : unit_(unit), diag_(diag) {
    for (const ClassDecl* cls : AllClassDecls(&unit)) {
      for (const ClassMember* m : cls->members) {
        if (m->nested_class != nullptr) outer_[m->nested_class] = cls;
      }
    }
  }

  // The type `type` written at `loc`, judged by both rules.
  void Type(const DataType& type, SourceLoc loc,
            const std::unordered_set<std::string_view>& local = {}) {
    Prefix(type, loc);
    Default(type, loc, local);
  }

  // §8.25.1: `type` written at `loc` behind the unadorned name of a
  // parameterized class, C::T, where the explicit specialization C#()::T is
  // required: anywhere but inside that class, the classes nested in it and
  // its out-of-block declarations, the names inside_ holds.
  void Prefix(const DataType& type, SourceLoc loc) {
    if (type.scope_name.empty() || type.scope_param_assignment_written ||
        inside_.contains(type.scope_name)) {
      return;
    }
    const ClassDecl* cls = FindClassDecl(type.scope_name, &unit_);
    if (cls == nullptr || cls->params.empty()) return;
    diag_.Error(loc,
                std::format("unadorned name '{}' used as scope resolution "
                            "prefix for parameterized class; use explicit "
                            "specialization '{}#(...)::' or '{}#()::'",
                            cls->name, cls->name, cls->name),
                Subclause("8.25.1"));
  }

  // §8.25: the type `type` written at `loc`, unless `local` holds its name: a
  // type parameter or typedef of the class the type is written in, which names
  // no class of the scope around it.
  void Default(const DataType& type, SourceLoc loc,
               const std::unordered_set<std::string_view>& local) {
    if (type.kind != DataTypeKind::kNamed || !type.type_params.empty() ||
        !type.scope_name.empty() || local.contains(type.type_name)) {
      return;
    }
    Class(type.type_name, loc);
  }

  // The class named `name` used with no arguments at `loc`.
  void Class(std::string_view name, SourceLoc loc) {
    Class(FindClassDecl(name, &unit_), loc);
  }

  // The class `cls` used with no arguments at `loc`; nothing where it is null.
  void Class(const ClassDecl* cls, SourceLoc loc) {
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

  // A class's base, properties, typedefs and methods, written inside it and
  // inside each class it is nested in.
  void ClassBody(const ClassDecl& cls) {
    inside_.clear();
    for (const ClassDecl* c = &cls; c != nullptr; c = Outer(*c)) {
      inside_.insert(c->name);
    }
    if (!cls.base_class.empty() && cls.base_class_type_params.empty() &&
        cls.extends_args.empty() && !cls.extends_has_default) {
      Class(FindBaseClass(&cls, &unit_), cls.range.start);
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
    inside_.clear();
  }

 private:
  // The class `cls` is nested in; null for one no class holds.
  const ClassDecl* Outer(const ClassDecl& cls) const {
    const auto kFound = outer_.find(&cls);
    return kFound == outer_.end() ? nullptr : kFound->second;
  }

  void Item(const ModuleItem& item, bool with_vars) {
    if (item.kind == ModuleItemKind::kVarDecl) {
      if (with_vars) {
        Type(item.data_type, item.loc);
      } else {
        Prefix(item.data_type, item.loc);
      }
    } else if (item.kind == ModuleItemKind::kTypedef) {
      Type(item.typedef_type, item.loc);
    } else if (item.kind == ModuleItemKind::kFunctionDecl ||
               item.kind == ModuleItemKind::kTaskDecl) {
      // §8.24: an out-of-block declaration is written inside its class.
      if (!item.method_class.empty()) inside_.insert(item.method_class);
      Subroutine(item);
      inside_.clear();
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
  // Each nested class's enclosing class (§8.23).
  std::unordered_map<const ClassDecl*, const ClassDecl*> outer_;
  // The names of the classes the declaration in hand is written inside.
  std::unordered_set<std::string_view> inside_;
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
