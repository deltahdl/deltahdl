#pragma once

namespace delta {

class DiagEngine;
struct DataType;
struct ModuleItem;

bool IsImplicitResultType(const DataType& result);

void ValidateExternTfPrototype(DiagEngine& diag, const ModuleItem* item);

void ValidateClassMethodPrototype(DiagEngine& diag, const ModuleItem* item);

}  // namespace delta
