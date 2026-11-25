#pragma once

#include <cstddef>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
class ValueScopes;
struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct Expr;
struct NameScope;

struct TypeParameterOf {
  std::string_view name;
  std::string_view owner;
};

std::string_view AssignedParameter(const ClassDecl& cls,
                                   const DataType& assignment,
                                   std::size_t index);

bool AssignsTypeParameter(const ClassDecl* cls, const DataType& assignment,
                          std::size_t index);

bool WritesValueArgument(const ClassDecl* cls, const DataType& assignment,
                         std::size_t index);

void ReportTypeParamSetToNoType(std::string_view name, SourceLoc loc,
                                DiagEngine& diag);

void ReportTypeParamAssignedNoType(const TypeParameterOf& param, SourceLoc loc,
                                   DiagEngine& diag);

bool WritesNoType(const Expr& written, const ValueScopes& scopes,
                  const NameScope& scope);

bool WritesNoType(const DataType& written, const ValueScopes& scopes,
                  const NameScope& scope);

void ReportTypeParametersSetToNoTypes(const CompilationUnit& unit,
                                      DiagEngine& diag);

}  // namespace delta
