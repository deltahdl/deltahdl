#pragma once

#include <vector>

#include "simulator/vpi_object.h"

namespace delta {

bool VpiIsSimpleExpr(VpiHandle obj);

bool VpiExpressionUses(const VpiObject* node, const VpiObject& expr);

bool VpiUsesExpr(const VpiObject& use, const VpiObject& expr);

std::vector<VpiObject*> VpiSimpleExprUses(VpiHandle expr);

}  // namespace delta
