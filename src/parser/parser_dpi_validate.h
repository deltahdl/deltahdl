#pragma once

#include <cstdint>

namespace delta {

class DiagEngine;
struct DataType;
struct ModuleItem;

// §35.5.5: validate the (already-parsed) result type of a DPI imported
// function. The type must be stated explicitly and restricted to small values.
void ValidateDpiResultType(DiagEngine& diag, const ModuleItem* item);

// §35.5.4: the ref qualifier is forbidden on the formal arguments of a DPI
// import declaration.
void ValidateDpiImportNoRefArgs(DiagEngine& diag, const ModuleItem* item);

// §35.5.6: why a formal argument's type falls outside the set of types the
// clause permits for a DPI subroutine, or kPermitted when it does not.
enum class DpiFormalTypeVerdict : uint8_t {
  kPermitted,
  kNotPermittedType,
  kUnpackedUnion,
};

// §35.5.6: decide whether one formal argument's type is among the types the
// clause permits, for an imported and an exported subroutine alike. A struct or
// union is decided by its members as well as by itself, since the clause
// permits an aggregate only where it is constructed from the supported types.
DpiFormalTypeVerdict ClassifyDpiFormalType(const DataType& type);

// §35.5.6: report each formal argument of an import declaration whose type the
// clause does not permit. The rule itself is ClassifyDpiFormalType; this states
// it in the wording an imported subroutine's diagnostic uses.
void ValidateDpiImportFormalTypes(DiagEngine& diag, const ModuleItem* item);

// §H.2: a formal argument that leaves its packed range unspecified is matched
// by every packed dimension of an actual collectively, so the unspecified one
// must be the only packed dimension the formal has.
void ValidateDpiImportOpenArrayPackedDims(DiagEngine& diag,
                                          const ModuleItem* item);

}  // namespace delta
