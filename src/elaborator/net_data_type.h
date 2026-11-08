#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_eval.h"

namespace delta {

struct DataType;
struct Expr;
struct ModuleItem;

struct TypeShapeTables {
  const TypedefMap& typedefs;
  const std::unordered_map<std::string_view, std::vector<Expr*>>& typedef_dims;
  const std::unordered_set<std::string_view>& class_names;
};

const DataType* FollowTypedefs(const DataType& dtype,
                               const TypedefMap& typedefs,
                               std::vector<std::string_view>& names);

bool IsFixedSizeUnpackedDim(const Expr* dim, const TypeShapeTables& tables);

void ValidateNetDeclaratorDims(const std::vector<Expr*>& dims,
                               const TypeShapeTables& tables, DiagEngine& diag,
                               SourceLoc loc);

void ValidateNetDataTypeIs4State(const DataType& dtype,
                                 const TypedefMap& typedefs, DiagEngine& diag,
                                 SourceLoc loc);

bool TypedefDimsAreFixedSize(const DataType& dtype,
                             const TypeShapeTables& tables);

void ValidateNetTypedefDims(const DataType& dtype,
                            const TypeShapeTables& tables, DiagEngine& diag,
                            SourceLoc loc);

std::string NamedTypeKey(std::string_view scope, std::string_view name);
std::string NamedTypeKey(const DataType& type);

bool IsLegalNettypeDataType(const DataType& dtype,
                            const TypeShapeTables& tables);

void ReportIllegalNettypeDataType(
    const ModuleItem& nettype, const TypeShapeTables& tables, DiagEngine& diag,
    const std::function<bool(std::string_view)>& names_covergroup = {});

}  // namespace delta
