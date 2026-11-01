#pragma once

#include <cstdint>
#include <functional>
#include <optional>
#include <span>
#include <string_view>

#include "common/source_loc.h"
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

}  // namespace delta
