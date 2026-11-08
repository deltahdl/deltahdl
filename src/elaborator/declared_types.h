#pragma once

#include <functional>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/aggregate_shape.h"

namespace delta {

struct CompilationUnit;
struct DataType;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

struct DeclaredType {
  const DataType& type;
  const std::vector<Expr*>& unpacked_dims;
  SourceLoc loc;
  const ModuleItem* nettype = nullptr;
};

using DeclaredTypeVisit = std::function<void(const DeclaredType&)>;

void ForEachInnerDeclaredType(const ModuleDecl* decl,
                              const DeclaredTypeVisit& visit);

void ForEachUnitDeclaredType(const CompilationUnit* unit,
                             const DeclaredTypeVisit& visit);

void CheckDeclaredTypeRules(
    const DeclaredType& declared, const AggregateShapeCtx& ctx,
    const std::function<bool(std::string_view)>& names_covergroup = {});

}  // namespace delta
