#include "elaborator/class_default_specialization.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <initializer_list>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct WrittenArgument {
  std::string_view name;
  bool gives_value = false;
};

using WrittenArguments = std::vector<WrittenArgument>;

WrittenArguments ArgumentsOf(const std::vector<DataType>& types) {
  WrittenArguments args;
  for (const DataType& type : types) {
    args.push_back({type.param_arg_name, type.kind != DataTypeKind::kImplicit ||
                                             type.type_ref_expr != nullptr});
  }
  return args;
}

WrittenArguments ArgumentsOf(const Expr& specialization) {
  WrittenArguments args;
  for (std::size_t i = 0; i < specialization.elements.size(); ++i) {
    args.push_back(
        {specialization.arg_names[i], specialization.elements[i] != nullptr});
  }
  return args;
}

WrittenArguments ArgumentsOfName(const DataType& named) {
  if (named.scope_param_assignment_written && !named.param_assignment_written) {
    return {};
  }
  return ArgumentsOf(named.type_params);
}

const WrittenArgument* ArgumentFor(const WrittenArguments& args,
                                   std::size_t ordinal, std::string_view name) {
  const auto kByName = std::ranges::find_if(
      args, [name](const WrittenArgument& arg) { return arg.name == name; });
  if (kByName != args.end()) return &*kByName;
  const bool kNamed = std::ranges::any_of(
      args, [](const WrittenArgument& arg) { return !arg.name.empty(); });
  return !kNamed && ordinal < args.size() ? &args[ordinal] : nullptr;
}

bool HasDefault(const ClassDecl& cls, std::size_t index) {
  const auto& [name, value] = cls.params[index];
  return cls.type_param_names.contains(name)
             ? cls.param_types.at(index).kind != DataTypeKind::kImplicit
             : value != nullptr;
}

std::string_view ParameterLeftWithoutValue(const ClassDecl& cls,
                                           const WrittenArguments& args) {
  std::size_t ordinal = 0;
  for (std::size_t i = 0; i < cls.params.size(); ++i) {
    const std::string_view kName = cls.params[i].first;
    if (cls.localparam_port_names.contains(kName)) continue;
    const WrittenArgument* arg = ArgumentFor(args, ordinal++, kName);
    if (HasDefault(cls, i)) continue;
    if (arg == nullptr || !arg->gives_value) return kName;
  }
  return {};
}

void ReportParameterLeftWithoutValue(const ClassDecl* cls,
                                     const WrittenArguments& args,
                                     SourceLoc loc, DiagEngine& diag) {
  if (cls == nullptr) return;
  const std::string_view kUnset = ParameterLeftWithoutValue(*cls, args);
  if (kUnset.empty()) return;
  if (args.empty()) {
    diag.ErrorOnce(loc,
                   std::format("parameterized class '{}' has no default "
                               "specialization; parameter '{}' has no default "
                               "value",
                               cls->name, kUnset),
                   Subclause("8.25"));
    return;
  }
  diag.ErrorOnce(loc,
                 std::format("specialization of parameterized class '{}' "
                             "gives no value to parameter '{}', which has no "
                             "default value",
                             cls->name, kUnset),
                 Subclause("8.25"));
}

DataType MemberType(const StructMember& member) {
  if (member.nested_type != nullptr) return *member.nested_type;
  DataType type;
  type.kind = member.type_kind;
  type.type_name = member.type_name;
  type.scope_name = member.scope_name;
  type.type_params = member.type_params;
  return type;
}

class SpecializationWalk {
 public:
  SpecializationWalk(const CompilationUnit& unit, DiagEngine& diag)
      : unit_(unit), diag_(diag) {
    for (const ClassDecl* cls : AllClassDecls(&unit)) {
      for (const ClassMember* m : cls->members) {
        if (m->nested_class != nullptr) outer_[m->nested_class] = cls;
      }
    }
  }

  void Items(const std::vector<ModuleItem*>& items) {
    for (const ModuleItem* item : items) Item(*item);
  }

  void Module(const ModuleDecl& decl) {
    for (const PortDecl& port : decl.ports) Type(port.data_type, port.loc);
    for (const DataType& type : decl.param_types) Type(type, decl.range.start);
    for (const auto& [name, value] : decl.params) Expression(value);
    Items(decl.items);
  }

  void ClassBody(const ClassDecl& cls) {
    for (const ClassDecl* c = &cls; c != nullptr; c = Outer(*c)) {
      inside_.insert(c->name);
    }
    local_ = cls.type_param_names;
    for (const ClassMember* m : cls.members) {
      if (m->typedef_item != nullptr) local_.insert(m->name);
    }
    Header(cls);
    for (const ClassMember* m : cls.members) Member(*m);
    inside_.clear();
    local_.clear();
  }

 private:
  const ClassDecl* Outer(const ClassDecl& cls) const {
    const auto kFound = outer_.find(&cls);
    return kFound == outer_.end() ? nullptr : kFound->second;
  }

  const ClassDecl* ClassNamed(const DataType& named) const {
    if (named.scope_name.empty()) {
      return FindClassDecl(named.type_name, &unit_);
    }
    const ClassDecl* in_package =
        FindClassInPackage(named.scope_name, named.type_name, &unit_);
    if (in_package != nullptr) return in_package;
    const ClassDecl* enclosing = FindClassDecl(named.scope_name, &unit_);
    return enclosing == nullptr ? nullptr
                                : FindNestedClass(enclosing, named.type_name);
  }

  void Judge(const ClassDecl* cls, const WrittenArguments& args,
             SourceLoc loc) {
    ReportParameterLeftWithoutValue(cls, args, loc, diag_);
  }

  void UnadornedPrefix(const DataType& type, SourceLoc loc) {
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

  void Type(const DataType& type, SourceLoc loc) {
    UnadornedPrefix(type, loc);
    for (const DataType& scope : type.specialized_scopes) {
      Judge(ClassNamed(scope), ArgumentsOf(scope.type_params), loc);
      Arguments(scope.type_params, loc);
    }
    const bool kShadowed =
        type.scope_name.empty() && local_.contains(type.type_name);
    if (type.kind == DataTypeKind::kNamed && !kShadowed) {
      Judge(ClassNamed(type), ArgumentsOfName(type), loc);
    }
    if (!type.scope_param_assignment_written || type.param_assignment_written) {
      Arguments(type.type_params, loc);
    }
    for (const StructMember& member : type.struct_members) {
      Type(MemberType(member), loc);
    }
    Expression(type.packed_dim_left);
    Expression(type.packed_dim_right);
  }

  void Arguments(const std::vector<DataType>& args, SourceLoc loc) {
    for (const DataType& arg : args) {
      Type(arg, loc);
      Expression(arg.type_ref_expr);
    }
  }

  void ClassNameOperand(const Expr* e) {
    if (e == nullptr || e->kind != ExprKind::kIdentifier || e->has_param_spec) {
      return;
    }
    Judge(FindClassDecl(e->text, &unit_), {}, e->range.start);
  }

  void Expression(const Expr* e) {
    if (e == nullptr) return;
    if (e->kind == ExprKind::kIdentifier && e->has_param_spec) {
      Judge(FindClassDecl(e->text, &unit_), ArgumentsOf(*e), e->range.start);
      for (const Expr* argument : e->elements) ClassNameOperand(argument);
    }
    if (e->type_value != nullptr) Type(*e->type_value, e->range.start);
    ForEachExprChild(e, [this](const Expr* child) { Expression(child); });
  }

  void Statement(const Stmt* s) {
    if (s == nullptr) return;
    if (s->kind == StmtKind::kVarDecl) Type(s->var_decl_type, s->range.start);
    for (const DataType& type : s->for_init_types) Type(type, s->range.start);
    ForEachChildExpr(s, [this](const Expr* e) { Expression(e); });
    ForEachChildStmt(s, [this](const Stmt* sub) { Statement(sub); });
  }

  void Subroutine(const ModuleItem& sub) {
    Type(sub.return_type, sub.loc);
    for (const FunctionArg& arg : sub.func_args) {
      Type(arg.data_type, sub.loc);
      Expression(arg.default_value);
    }
    for (const Stmt* s : sub.func_body_stmts) Statement(s);
  }

  void Header(const ClassDecl& cls) {
    const SourceLoc kLoc = cls.range.start;
    if (!local_.contains(cls.base_class)) {
      Judge(FindBaseClass(&cls, &unit_),
            ArgumentsOf(cls.base_class_type_params), kLoc);
    }
    Arguments(cls.base_class_type_params, kLoc);
    for (const Expr* argument : cls.extends_args) Expression(argument);
    for (const auto* refs : {&cls.extends_interfaces, &cls.implements_types}) {
      for (const InterfaceRef& ref : *refs) {
        Judge(FindReferencedClass(ref, &unit_), ArgumentsOf(ref.type_params),
              kLoc);
        Arguments(ref.type_params, kLoc);
      }
    }
    for (const DataType& type : cls.param_types) Type(type, kLoc);
    for (const auto& [name, value] : cls.params) Expression(value);
  }

  void Member(const ClassMember& m) {
    if (m.method != nullptr) {
      Subroutine(*m.method);
    } else if (m.typedef_item != nullptr) {
      Type(m.typedef_item->typedef_type, m.loc);
    } else if (m.kind == ClassMemberKind::kProperty) {
      Type(m.data_type, m.loc);
    }
    Expression(m.init_expr);
    for (const Expr* dim : m.unpacked_dims) Expression(dim);
    for (const Expr* relation : m.constraint_exprs) Expression(relation);
  }

  void Item(const ModuleItem& item) {
    Type(item.data_type, item.loc);
    Type(item.typedef_type, item.loc);
    if (item.kind == ModuleItemKind::kFunctionDecl ||
        item.kind == ModuleItemKind::kTaskDecl) {
      if (!item.method_class.empty()) inside_.insert(item.method_class);
      Subroutine(item);
      inside_.clear();
    }
    Expression(item.init_expr);
    Expression(item.assign_rhs);
    Expression(item.gen_cond);
    for (const Expr* dim : item.unpacked_dims) Expression(dim);
    for (const auto& [name, value] : item.inst_params) {
      Expression(value);
      ClassNameOperand(value);
    }
    Statement(item.body);
    Items(item.gen_body);
    if (item.gen_else != nullptr) Item(*item.gen_else);
    for (const GenerateCaseItem& arm : item.gen_case_items) Items(arm.body);
  }

  const CompilationUnit& unit_;
  DiagEngine& diag_;
  std::unordered_map<const ClassDecl*, const ClassDecl*> outer_;
  std::unordered_set<std::string_view> inside_;
  std::unordered_set<std::string_view> local_;
};

}  // namespace

void ReportSpecializationWithoutValue(const DataType& named, SourceLoc loc,
                                      const CompilationUnit& unit,
                                      DiagEngine& diag) {
  ReportParameterLeftWithoutValue(FindClassDecl(named.type_name, &unit),
                                  ArgumentsOfName(named), loc, diag);
}

void ReportClassSpecializationsWithoutValues(const CompilationUnit& unit,
                                             DiagEngine& diag) {
  SpecializationWalk walk(unit, diag);
  walk.Items(unit.cu_items);
  for (const auto* group :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *group) walk.Module(*decl);
  }
  for (const PackageDecl* package : unit.packages) walk.Items(package->items);
  for (const ClassDecl* cls : AllClassDecls(&unit)) walk.ClassBody(*cls);
}

}  // namespace delta
