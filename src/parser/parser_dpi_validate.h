#pragma once

namespace delta {

class DiagEngine;
struct ModuleItem;

// §35.5.5: validate the (already-parsed) result type of a DPI imported
// function. The type must be stated explicitly and restricted to small values.
void ValidateDpiResultType(DiagEngine& diag, const ModuleItem* item);

// §35.5.4: the ref qualifier is forbidden on the formal arguments of a DPI
// import declaration.
void ValidateDpiImportNoRefArgs(DiagEngine& diag, const ModuleItem* item);

// §35.5.6: the listed types are the only permitted types for formal arguments
// of imported subroutines; a union argument must additionally be packed.
void ValidateDpiImportFormalTypes(DiagEngine& diag, const ModuleItem* item);

}  // namespace delta
