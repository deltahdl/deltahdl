#include "elaborator/specialization_type_arguments.h"

#include <cstddef>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/scoped_walk.h"
#include "elaborator/std_package.h"
#include "elaborator/type_parameter_values.h"
#include "elaborator/type_spelled_by.h"
#include "elaborator/value_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool TakesOneType(const DataType& named) {
  return named.type_name == "mailbox" || named.type_name == "weak_reference";
}

class TypeArgumentReader : public ScopedWalk {
 public:
  using ScopedWalk::ScopedWalk;

 private:
  void VisitExpr(const Expr&, const NameScope&) override {}

  void VisitType(const DataType& type, SourceLoc,
                 const NameScope& scope) override {
    for (const DataType& specialized : type.specialized_scopes) {
      ReadArguments(specialized, specialized.type_params, scope);
    }
    if (type.kind == DataTypeKind::kNamed) ReadArgumentsOfLast(type, scope);
    for (const StructMember& member : type.struct_members) {
      ReadArguments(Named(member.scope_name, member.type_name),
                    member.type_params, scope);
      if (member.nested_type != nullptr) {
        VisitType(*member.nested_type, {}, scope);
      }
    }
  }

  void VisitClass(const ClassDecl& cls, const NameScope& scope) override {
    ReadArguments(Named(cls.base_class_scope, cls.base_class),
                  cls.base_class_type_params, *scope.outer);
    for (const auto* refs : {&cls.extends_interfaces, &cls.implements_types}) {
      for (const InterfaceRef& ref : *refs) {
        ReadArguments(Named(ref.scope, ref.name), ref.type_params,
                      *scope.outer);
      }
    }
  }

  static DataType Named(std::string_view scope_name, std::string_view name) {
    DataType named;
    named.kind = DataTypeKind::kNamed;
    named.scope_name = scope_name;
    named.type_name = name;
    return named;
  }

  void ReadArgumentsOfLast(const DataType& type, const NameScope& scope) {
    const bool kOfTheScope =
        type.scope_param_assignment_written && !type.param_assignment_written;
    ReadArguments(kOfTheScope ? type.specialized_scopes.back() : type,
                  type.type_params, scope);
  }

  void ReadArguments(const DataType& named,
                     const std::vector<DataType>& arguments,
                     const NameScope& scope) {
    if (arguments.empty()) return;
    const ClassDecl* cls = Scopes().ClassDeclaredAs(named, scope);
    for (std::size_t i = 0; i < arguments.size(); ++i) {
      const bool kGivesAType = cls == nullptr
                                   ? TakesOneType(named)
                                   : AssignsTypeParameter(cls, arguments[i], i);
      if (kGivesAType) Read(arguments[i], scope);
    }
  }

  void Read(const DataType& argument, const NameScope& scope) const {
    if (argument.type_ref_expr == nullptr) return;
    DataType type = TypeSpelledBy(argument.type_ref_expr);
    if (type.scope_name.empty()) return;
    const bool kNamesAClassOfStd =
        type.scope_name == "std" && IsStdPackageSystemType(type.type_name);
    if (!kNamesAClassOfStd && !Scopes().NamesType(type, scope)) return;
    type.param_arg_name = argument.param_arg_name;
    const_cast<DataType&>(argument) = type;
  }
};

}  // namespace

void ReadScopedTypeArguments(const CompilationUnit& unit) {
  TypeArgumentReader(unit).WalkUnit(unit);
}

}  // namespace delta
