#pragma once

#include <cstdint>

namespace delta {

class DiagEngine;
struct DataType;
struct ModuleItem;

void ValidateDpiResultType(DiagEngine& diag, const ModuleItem* item);

void ValidateDpiImportNoRefArgs(DiagEngine& diag, const ModuleItem* item);

enum class DpiFormalTypeVerdict : uint8_t {
  kPermitted,
  kNotPermittedType,
  kUnpackedUnion,
};

DpiFormalTypeVerdict ClassifyDpiFormalType(const DataType& type);

void ValidateDpiImportFormalTypes(DiagEngine& diag, const ModuleItem* item);

void ValidateDpiImportOpenArrayPackedDims(DiagEngine& diag,
                                          const ModuleItem* item);

}  // namespace delta
