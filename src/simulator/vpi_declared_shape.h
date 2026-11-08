#pragma once

#include "parser/ast_type.h"
#include "simulator/vpi_object.h"

namespace delta {

void VpiRecordDeclaredShape(VpiObject* var, const DataType& type);

}  // namespace delta
