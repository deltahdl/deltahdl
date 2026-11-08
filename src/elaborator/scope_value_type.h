#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <string_view>

#include "common/source_loc.h"
#include "elaborator/expression_self_type.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class Arena;
struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;
struct RtlirModule;

struct ValueShape {
  uint32_t width = 0;
  bool is_signed = false;
};

using ValueShapeOf = std::function<std::optional<ValueShape>(std::string_view)>;

struct TypeRefScope {
  const RtlirModule* mod;
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  SourceLoc reference;
  Arena& arena;
  const ModuleDecl* decl;
};

void SetTypeRefPackedDims(DataType& dt, uint32_t width, Arena& arena);

void AdoptLogicVector(DataType& dt, ValueShape shape, Arena& arena);

const ModuleItem* ItemNamed(std::span<ModuleItem* const> items,
                            std::string_view name);

const PackageDecl* PackageDeclaring(
    const CompilationUnit* unit, std::string_view name,
    const std::function<bool(std::string_view)>& reaches);

DataType DeclaredValueType(const ModuleItem& item, const ValueShapeOf& shape_of,
                           Arena& arena);

DataType ScopeValueType(const ModuleItem& item,
                        std::span<ModuleItem* const> items, Arena& arena);

std::optional<ValueShape> EnumConstantShape(std::string_view name,
                                            std::span<ModuleItem* const> items);

std::optional<ValueShape> ScopeValueShape(std::string_view name,
                                          std::span<ModuleItem* const> items,
                                          Arena& arena);

std::optional<DataType> OuterValueType(std::string_view name,
                                       const TypeRefScope& scope);

const PackageDecl* PackageNamed(const CompilationUnit& unit,
                                std::string_view name);

struct OuterScope {
  const CompilationUnit* unit;
  const ModuleDecl* reference;
  const TypeShapeTables& tables;
  Arena& arena;
};

std::optional<DeclaredValue> ScopeValue(std::span<ModuleItem* const> items,
                                        std::string_view scope,
                                        std::string_view name,
                                        const OuterScope& outer);

std::optional<DeclaredValue> ScopedValue(std::string_view prefix,
                                         std::string_view name,
                                         const OuterScope& outer);

std::optional<DeclaredValue> ImportedValue(std::span<ModuleItem* const> items,
                                           std::string_view name,
                                           const OuterScope& outer);

std::optional<DeclaredValue> OuterValue(const RtlirModule& mod,
                                        std::string_view name,
                                        const OuterScope& outer);

}  // namespace delta
