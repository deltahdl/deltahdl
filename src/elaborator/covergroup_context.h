#ifndef DELTA_ELABORATOR_COVERGROUP_CONTEXT_H
#define DELTA_ELABORATOR_COVERGROUP_CONTEXT_H

#include <functional>
#include <optional>
#include <string_view>

#include "elaborator/coverpoint_bin_set_expression.h"
#include "elaborator/value_kind.h"
#include "parser/ast_type.h"

namespace delta {

struct CoverPointDecl;
struct CovergroupDecl;
struct Expr;
struct ModuleItem;

using CovergroupTypeOf =
    std::function<std::optional<DataTypeKind>(std::string_view)>;
using CovergroupDeclared = std::function<bool(std::string_view)>;

struct CovergroupArrays {
  std::function<std::optional<SetExpressionArrayKind>(std::string_view)>
      kind_of;
  CovergroupDeclared is_type;
};

using CovergroupValueKind = std::function<ValueKind(const Expr*)>;

using CovergroupFunction = std::function<const ModuleItem*(std::string_view)>;

struct CovergroupContext {
  CovergroupTypeOf type_of;
  CovergroupDeclared declared;
  CovergroupArrays arrays;
  CovergroupValueKind value_kind;
  CovergroupDeclared non_constant;
  CovergroupFunction function_named;
  CovergroupDeclared is_class;
};

const FunctionArg* FindCovergroupFormal(const CovergroupDecl& cg,
                                        std::string_view name);

bool IsRefCovergroupFormal(const CovergroupDecl& cg, std::string_view name);

ValueKind KindOfDeclaredType(const DataType& type,
                             const CovergroupDeclared& is_class);

std::string_view CoverpointName(const CoverPointDecl& cp);

}  // namespace delta

#endif
