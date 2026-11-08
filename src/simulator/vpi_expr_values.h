#pragma once

#include "common/types.h"

namespace delta {

class SimContext;
class VpiContext;
struct VpiExprScope;
struct VpiObject;

Logic4Vec VpiEvaluateWhereWritten(const VpiExprScope& scope, SimContext& sim);

Logic4Vec VpiEvaluateExpressionObject(const VpiObject& obj, SimContext& sim);

void VpiWatchContAssignChanges(VpiContext& vpi, VpiObject* obj,
                               SimContext* sim);

VpiObject* VpiVarSelectElement(const VpiObject& select, SimContext* sim);

}  // namespace delta
