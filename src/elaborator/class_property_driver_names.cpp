#include "elaborator/class_property_driver_names.h"

#include <cstddef>
#include <format>
#include <optional>
#include <string>
#include <utility>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/type_spelled_by.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

ClassPropertyDriverNames::ClassPropertyDriverNames(
    ClassOfType class_of, const ClassPropertyTables& tables)
    : class_of_(std::move(class_of)), tables_(tables) {}

bool ClassPropertyDriverNames::NamesClassScope(const Expr& access) const {
  return access.is_scope_resolution && access.rhs != nullptr &&
         class_of_(TypeSpelledBy(access.lhs)).has_value();
}

const Expr* ClassPropertyDriverNames::ClassScopedAccess(
    const Expr* target) const {
  const Expr* at = target;
  while (at->kind == ExprKind::kSelect ||
         (at->kind == ExprKind::kMemberAccess && !NamesClassScope(*at))) {
    at = at->kind == ExprKind::kSelect ? at->base : at->lhs;
  }
  return at->kind == ExprKind::kMemberAccess ? at : nullptr;
}

std::string ClassPropertyDriverNames::NameOf(const ClassSpecialization& owner) {
  std::size_t i = 0;
  while (i < seen_.size() &&
         !SameSpecialization(seen_[i], owner, tables_.scope, tables_.typedefs)
              .value_or(false)) {
    ++i;
  }
  if (i == seen_.size()) seen_.push_back(owner);
  return std::format("{}#{}", owner.cls->name, i);
}

std::optional<std::string>
ClassPropertyDriverNames::DeclaringSpecializationName(const Expr& access) {
  const std::optional<ClassSpecialization> kWritten =
      class_of_(spelled_.emplace_back(TypeSpelledBy(access.lhs)));
  if (!kWritten) return std::nullopt;
  ClassSpecialization owner = *kWritten;
  const OwnedMember kOwned =
      FindMemberAndOwner(owner.cls, access.rhs->text, tables_.unit);
  while (kOwned.owner != nullptr && owner.cls != kOwned.owner &&
         owner.args != nullptr) {
    owner = {FindBaseClass(owner.cls, tables_.unit),
             SpecializedExtendsArguments(owner, tables_.scope, tables_.typedefs,
                                         tables_.arena)};
  }
  if (kOwned.owner == nullptr || owner.args == nullptr) return std::nullopt;
  return NameOf(owner);
}

std::string ClassPropertyDriverNames::WrittenPrefix(const Expr* target) const {
  return LongestStaticPrefix(target, tables_.scope);
}

std::string ClassPropertyDriverNames::DriverPrefix(const Expr* target) {
  std::string prefix = WrittenPrefix(target);
  const Expr* access = ClassScopedAccess(target);
  if (access == nullptr) return prefix;
  const std::size_t kWritten = WrittenPrefix(access->lhs).size();
  std::optional<std::string> name = DeclaringSpecializationName(*access);
  return name ? *name + prefix.substr(kWritten) : prefix;
}

}  // namespace delta
