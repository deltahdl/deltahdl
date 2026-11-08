#pragma once

#include <cstddef>
#include <functional>

#include "elaborator/type_site_lookup.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct DataType;
struct Expr;

struct SitedType {
  const DataType* type = nullptr;
  TypeSite site = {};
  std::size_t dims = 0;
};

SitedType ThroughTypedefsAt(const CompilationUnit& unit, SitedType named);

using RootTypeOf = std::function<SitedType(const Expr& root)>;

void ReportUndeclaredAggregateMember(const Expr& access,
                                     const CompilationUnit& unit,
                                     const RootTypeOf& root_type,
                                     DiagEngine& diag);

}  // namespace delta
