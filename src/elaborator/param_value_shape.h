#pragma once

#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/param_value_assignability.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;
struct RtlirParamDecl;

ParamValueShape ShapeOfIdentity(ParamValueKind kind, const DataType& type);

ParamValueShape ParamTargetShape(const DataType& type,
                                 const std::vector<Expr*>& dims,
                                 const ParamValueScope& scope);

ParamValueShape ParamDeclTargetShape(const RtlirParamDecl& pd,
                                     const ParamValueScope& scope);

ParamValueShape ValueOrTargetShape(const ParamValueShape& target,
                                   const Expr* value,
                                   const ParamValueScope& scope);

std::optional<ParamValueShape> DeclaringEnumShape(const DataType* enumeration);

ParamValueShape ParamValueShapeOf(const Expr* value,
                                  const ParamValueScope& scope);

bool ParamShapeAssignable(const ParamValueShape& target,
                          const ParamValueShape& value,
                          const ParamValueScope& scope);

std::optional<ParamValueShape> ScopedParamShape(std::string_view owner,
                                                std::string_view name,
                                                const ParamValueScope& scope);

}  // namespace delta
