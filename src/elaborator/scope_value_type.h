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

// §6.20.2 with §26.2, §26.3 and §3.12.1: the type of a value a type reference
// names in a package or in the compilation unit, read in the scope declaring
// it.

namespace delta {

class Arena;
struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;
struct PackageDecl;
struct RtlirModule;

// The width and signing of a value a type reference's expression names.
struct ValueShape {
  uint32_t width = 0;
  bool is_signed = false;
};

// The shape of the value a name stands for in the scope an expression is
// written in, empty where the scope declares no value of the name.
using ValueShapeOf = std::function<std::optional<ValueShape>(std::string_view)>;

// What a type reference's argument is looked up in beyond the module's own
// variables and nets: the module, the typedefs in force, the compilation unit
// and the position of the declaration writing the reference, with the arena a
// resolved type's packed dimensions are made in, and the declaration of the
// module being elaborated, the last of Elaborator::module_decl_path_, within
// whose elaboration every type reference is resolved.
struct TypeRefScope {
  const RtlirModule* mod;
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  SourceLoc reference;
  Arena& arena;
  const ModuleDecl* decl;
};

// Builds on `dt` the packed dimension [width-1:0] of a type reference resolved
// to `width` bits.
void SetTypeRefPackedDims(DataType& dt, uint32_t width, Arena& arena);

// Takes onto `dt`, in place of its type reference, the logic vector of
// `shape`'s width and signing.
void AdoptLogicVector(DataType& dt, ValueShape shape, Arena& arena);

// The item of `items` written `name`, or null where none is.
const ModuleItem* ItemNamed(std::span<ModuleItem* const> items,
                            std::string_view name);

// The first package of `unit` that `reaches` answers true for and that
// declares an item written `name`, or null where none does.
const PackageDecl* PackageDeclaring(
    const CompilationUnit* unit, std::string_view name,
    const std::function<bool(std::string_view)>& reaches);

// The type of the value `item` declares, whose value's names `shape_of` reads.
DataType DeclaredValueType(const ModuleItem& item, const ValueShapeOf& shape_of,
                           Arena& arena);

// The type of the value `item` declares among `items`, the declarations of a
// package or of the compilation unit.
DataType ScopeValueType(const ModuleItem& item,
                        std::span<ModuleItem* const> items, Arena& arena);

// The shape of the enumeration constant `name` that one of `items` declares.
std::optional<ValueShape> EnumConstantShape(std::string_view name,
                                            std::span<ModuleItem* const> items);

// The shape of the parameter or enumeration constant `name` among `items`.
std::optional<ValueShape> ScopeValueShape(std::string_view name,
                                          std::span<ModuleItem* const> items,
                                          Arena& arena);

// The type of the value `name` names outside the module of `scope`.
std::optional<DataType> OuterValueType(std::string_view name,
                                       const TypeRefScope& scope);

// The package `unit` declares as `name`; null where it declares none.
const PackageDecl* PackageNamed(const CompilationUnit& unit,
                                std::string_view name);

// What a name an expression writes is looked up in beyond the module holding
// it: the compilation unit, null where none is known, the declaration of the
// module, whose position bounds the part of the unit a reference in it
// searches (§3.12.1), null where no module is being elaborated, the tables
// that tell the kind of array an unpacked dimension makes, and the arena a
// parameter's vector type is made in.
struct OuterScope {
  const CompilationUnit* unit;
  const ModuleDecl* reference;
  const TypeShapeTables& tables;
  Arena& arena;
};

// §6.23 with §26.2, §3.12.1 and §6.19.3: the value `name` stands for among
// `items`, the declarations of the package or of the compilation unit whose
// typedefs are read behind the scope `scope`: a variable's or net's type and
// unpacked dimensions, a value parameter's type (ScopeValueType), or an
// enumeration constant's, the typedef naming its enumeration or else the
// enumeration as written. A type the declaration writes by one of the scope's
// own typedef names is read behind `scope`, the key the typedef is recorded
// under. Nothing where `items` declare no value of the name.
std::optional<DeclaredValue> ScopeValue(std::span<ModuleItem* const> items,
                                        std::string_view scope,
                                        std::string_view name,
                                        const OuterScope& outer);

// §26.3 with §3.12.1: the value `name`, written behind the scope `prefix`,
// stands for: one the package of that name declares, or, behind `$unit`, one
// the compilation unit declares before the module. Nothing where the scope is
// neither, or declares no value of the name.
std::optional<DeclaredValue> ScopedValue(std::string_view prefix,
                                         std::string_view name,
                                         const OuterScope& outer);

// §26.3 with §3.12.1: the value the bare `name` stands for outside `mod`: one
// a package `mod` imports it from declares, or else one the compilation unit
// declares before the module. Nothing where neither declares a value of the
// name.
std::optional<DeclaredValue> OuterValue(const RtlirModule& mod,
                                        std::string_view name,
                                        const OuterScope& outer);

}  // namespace delta
