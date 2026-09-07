#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "parser/ast_type.h"

namespace delta {

struct CompilationUnit;
struct ImportItem;
struct ModuleItem;

// What a DPI declaration's type names stand for.
//
// §35.5.5 and §35.5.6 judge an imported subroutine's result and formals by the
// type behind the name rather than by the name, and §35.5.4's footnote 27 --
// "class types cannot be passed at all" -- by whether the name is a class. The
// parser can do neither: it holds every such type as a DataTypeKind::kNamed and
// has no table to look one up in. So the names are resolved here, over what the
// source around a declaration declares, and the clauses are applied to what
// they resolve to.

// §35.5.4 footnote 27: the class names a DPI check tells apart from a name it
// simply cannot see. An unresolved name is left alone -- it may be forward
// declared or imported -- so the prohibition needs the classes named outright.
using DpiClassNames = std::unordered_set<std::string_view>;

// §26.3: an import declaration makes a package's typedef nameable in the
// importing scope by its bare name, so a DPI formal written with that name is a
// typedef reference the §35.5.6 check has to follow. Adds the bare name for the
// declaration in hand.
void AddImportedTypedefs(const ImportItem& import_item,
                         const CompilationUnit* unit, TypedefMap& typedefs);

// The typedef names one scope resolves, which is `outer` plus the ones the
// scope declares and the ones its import declarations bring in.
TypedefMap DpiScopeTypedefs(const std::vector<ModuleItem*>& items,
                            const CompilationUnit* unit,
                            const TypedefMap& outer);

// The class names a DPI declaration in this unit can name. §3.12.1 puts a class
// declared outside every design element in the compilation-unit scope, which
// the parser keeps in its own list rather than among the unit's items, and that
// is where a source writes the class an import in a module names -- so both are
// walked.
DpiClassNames CollectDpiClassNames(
    const CompilationUnit* unit,
    const std::vector<const std::vector<ModuleItem*>*>& scopes);

// Follow a type name to the type it stands for. Returns the type passed in when
// nothing resolved, which leaves an unresolved name to be passed over.
DataType ResolveDpiTypeName(const DataType& type, const TypedefMap& typedefs);

// Whether `type`, followed through the scope's typedefs, names a class.
bool NamesAClass(const DataType& type, const TypedefMap& typedefs,
                 const DpiClassNames& classes);

}  // namespace delta
