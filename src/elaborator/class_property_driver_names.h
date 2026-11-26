#pragma once

#include <deque>
#include <functional>
#include <optional>
#include <string>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct Expr;

using ClassOfType =
    std::function<std::optional<ClassSpecialization>(const DataType&)>;

struct ClassPropertyTables {
  const CompilationUnit* unit;
  const ScopeMap& scope;
  const TypedefMap& typedefs;
  Arena& arena;
};

class ClassPropertyDriverNames {
 public:
  ClassPropertyDriverNames(ClassOfType class_of,
                           const ClassPropertyTables& tables);

  std::string WrittenPrefix(const Expr* target) const;
  std::string DriverPrefix(const Expr* target);

 private:
  bool NamesClassScope(const Expr& access) const;
  const Expr* ClassScopedAccess(const Expr* target) const;
  std::optional<std::string> DeclaringSpecializationName(const Expr& access);
  std::string NameOf(const ClassSpecialization& owner);

  ClassOfType class_of_;
  ClassPropertyTables tables_;
  std::deque<DataType> spelled_;
  std::vector<ClassSpecialization> seen_;
};

}  // namespace delta
