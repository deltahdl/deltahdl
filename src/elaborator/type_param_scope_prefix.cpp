#include "elaborator/type_param_scope_prefix.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

// §6.20.3: the check that a type parameter prefixing the class scope
// resolution operator resolves to a class, made with the type each instance
// binds the parameter to.

namespace delta {

// Whether `type` is a class or a name the scope does not resolve, following a
// typedef or type parameter naming another by a bare name to the type it ends
// at. Only a type that ends at something other than a name is known to be no
// class.
static bool MayBeClass(const DataType& type,
                       const TypeParamPrefixScope& scope) {
  const DataType* cur = &type;
  for (int depth = 0; depth < 32; ++depth) {
    if (cur->kind != DataTypeKind::kNamed) return false;
    if (!cur->scope_name.empty()) return true;
    if (scope.class_names.contains(cur->type_name)) return true;
    auto next = scope.typedefs.find(cur->type_name);
    if (next == scope.typedefs.end() || &next->second == cur) return true;
    cur = &next->second;
  }
  return true;
}

void ReportTypeParamPrefixNotAClass(std::string_view prefix, SourceLoc loc,
                                    const TypeParamPrefixScope& scope,
                                    DiagEngine& diag) {
  if (prefix.empty()) return;
  bool is_type_param =
      std::ranges::any_of(scope.params, [&](const RtlirParamDecl& p) {
        return p.is_type_param && p.name == prefix;
      });
  if (!is_type_param) return;
  auto bound = scope.typedefs.find(prefix);
  if (bound == scope.typedefs.end() || MayBeClass(bound->second, scope)) return;
  diag.ErrorOnce(loc,
                 std::format("type parameter '{}' used as a class scope "
                             "resolution prefix does not resolve to a class",
                             prefix),
                 Subclause("6.20.3"));
}

void ReportTypeRefPrefixNotAClass(const Expr* ref, SourceLoc loc,
                                  const TypeParamPrefixScope& scope,
                                  DiagEngine& diag) {
  if (ref->kind != ExprKind::kMemberAccess || !ref->is_scope_resolution ||
      ref->lhs == nullptr || ref->lhs->kind != ExprKind::kIdentifier)
    return;
  ReportTypeParamPrefixNotAClass(ref->lhs->text, loc, scope, diag);
}

const DataType* TypeRefThroughBoundPrefix(std::string_view prefix,
                                          std::string_view name,
                                          const TypedefMap& typedefs) {
  DataType written;
  written.kind = DataTypeKind::kNamed;
  written.scope_name = prefix;
  written.type_name = name;
  if (!ThroughBoundPrefix(written, typedefs).has_value()) return nullptr;
  return FindNamedType(written, typedefs);
}

// The type `cls` binds its type parameter at index `i`, named `name`, to under
// the actuals `written` gives: the one named for it, else the one at its
// position, else the class's default. Null where none is given.
static const DataType* BoundActual(const ClassDecl& cls, size_t i,
                                   std::string_view name,
                                   const DataType& written) {
  for (const DataType& actual : written.type_params) {
    if (actual.param_arg_name == name) return &actual;
  }
  if (i < written.type_params.size() &&
      written.type_params[i].param_arg_name.empty())
    return &written.type_params[i];
  if (i < cls.param_types.size()) return &cls.param_types[i];
  return nullptr;
}

// Whether the body of `cls` selects a type through its type parameter
// `name`, in a typedef or a body `localparam type` (carried as a typedef).
static bool BodySelectsThrough(const ClassDecl& cls, std::string_view name) {
  return std::ranges::any_of(cls.members, [&](const ClassMember* m) {
    return m->kind == ClassMemberKind::kTypedef && m->typedef_item != nullptr &&
           m->typedef_item->typedef_type.kind == DataTypeKind::kNamed &&
           m->typedef_item->typedef_type.scope_name == name &&
           m->typedef_item->typedef_type.outer_scope_names.empty();
  });
}

void ReportSpecializationPrefixNotAClass(const DataType& written, SourceLoc loc,
                                         const CompilationUnit* unit,
                                         DiagEngine& diag) {
  if (written.kind != DataTypeKind::kNamed || !written.scope_name.empty())
    return;
  const ClassDecl* cls = FindClassDecl(written.type_name, unit);
  if (cls == nullptr) return;
  for (size_t i = 0; i < cls->params.size(); ++i) {
    std::string_view name = cls->params[i].first;
    if (!cls->type_param_names.contains(name) ||
        !BodySelectsThrough(*cls, name))
      continue;
    const DataType* actual = BoundActual(*cls, i, name, written);
    if (actual == nullptr || actual->kind == DataTypeKind::kNamed ||
        actual->kind == DataTypeKind::kImplicit)
      continue;
    diag.ErrorOnce(loc,
                   std::format("type parameter '{}' used as a class scope "
                               "resolution prefix does not resolve to a class",
                               name),
                   Subclause("6.20.3"));
  }
}

void ReportUnitSpecializations(const CompilationUnit* unit, DiagEngine& diag) {
  for (const ModuleItem* item : unit->cu_items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      ReportSpecializationPrefixNotAClass(item->typedef_type, item->loc, unit,
                                          diag);
    } else if (item->kind == ModuleItemKind::kVarDecl) {
      ReportSpecializationPrefixNotAClass(item->data_type, item->loc, unit,
                                          diag);
    }
  }
  for (const ClassDecl* cls : unit->classes) {
    for (const ClassMember* m : cls->members) {
      if (m->kind == ClassMemberKind::kProperty) {
        ReportSpecializationPrefixNotAClass(m->data_type, m->loc, unit, diag);
      } else if (m->kind == ClassMemberKind::kTypedef &&
                 m->typedef_item != nullptr) {
        ReportSpecializationPrefixNotAClass(m->typedef_item->typedef_type,
                                            m->loc, unit, diag);
      }
    }
  }
}

}  // namespace delta
