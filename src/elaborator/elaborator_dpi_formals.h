#pragma once

#include "common/diagnostic.h"
#include "elaborator/elaborator_dpi_names.h"
#include "elaborator/type_eval.h"

namespace delta {

struct ModuleItem;

// §35.5.6: an imported subroutine's formal argument written as a typedef name
// is permitted only where the type behind the name is. The parser holds every
// such formal as a kNamed type and has no typedef table to look it up in, so
// the rule is enforced here, over the names the enclosing scope resolves. A
// name that does not resolve is left alone. The report names the typedef the
// source wrote, which is what a reader has in front of them, and one import
// reports once however many of its formals are at fault.
void CheckImportFormalTypedefTypes(const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag);

// §35.5.6: among the unpacked kinds, the permitted formal argument types of
// an import are the unpacked array and, per §35.5.6.1, the open array; a
// queue dimension (§7.10) or an associative one (§7.8) is neither, and the
// foreign side has no representation of either. The parser's check reads the
// formal's data type alone, and both dimensions stand on the formal's
// unpacked dimensions, so they are judged here, where the scope's typedef and
// class names tell an index type from a parameter sizing the dimension. One
// import reports once.
void CheckImportFormalUnpackedDims(const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag);

// §35.5.6 with §35.7: the same for an exported subroutine, `callable` being
// the SystemVerilog function or task the export declaration `item` names,
// whose formals the export holds to the import's restrictions; the dynamic
// array's absent dimension is the separate rule of the same subclause,
// reported by CheckExportDynamicArrayArguments in elaborator_dpi.cpp.
void CheckExportFormalUnpackedDims(const ModuleItem* callable,
                                   const ModuleItem* item,
                                   const TypedefMap& typedefs,
                                   const DpiClassNames& classes,
                                   DiagEngine& diag);

}  // namespace delta
