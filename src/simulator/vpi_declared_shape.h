#pragma once

#include "parser/ast_type.h"
#include "simulator/vpi_object.h"

namespace delta {

// §37.17 details 20 and 22: give the variable `var`, declared of `type`, the
// signing and the vpiScalar and vpiVector its declaration says -- for one no
// RtlirVariable records, a task's or function's argument (§37.13).
void VpiRecordDeclaredShape(VpiObject* var, const DataType& type);

}  // namespace delta
