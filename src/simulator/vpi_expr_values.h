#pragma once

#include "common/types.h"

namespace delta {

class SimContext;
class VpiContext;
struct VpiObject;

// §37.3.5 with §38.15: the value of `obj`, which holds no storage but stands
// for an expression, an operation, a call or a continuous assignment (its
// expr_scope records where): the expression evaluated where the source wrote
// it, by a stand-in process of the instance and generate blocks it stands in,
// as a process running there would read its names, and for an assignment at
// the width of the left side it drives.
Logic4Vec VpiEvaluateExpressionObject(const VpiObject& obj, SimContext& sim);

// §37.47 detail 2: watch the continuous assignment or cont assign bit `obj`,
// which holds no storage, for changes of its value, through the storage of
// every net and variable its right-hand side reads, calling back the
// cbValueChange registrations placed on it as its value changes, until none is
// left. Does nothing for any other object, or without the run `sim`.
void VpiWatchContAssignChanges(VpiContext& vpi, VpiObject* obj,
                               SimContext* sim);

}  // namespace delta
