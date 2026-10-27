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
// left. Does nothing for any other object, or without the run `sim`. `obj` is
// never null, and a continuous assignment or cont assign bit carries the
// expr_scope the design gives every one of them.
void VpiWatchContAssignChanges(VpiContext& vpi, VpiObject* obj,
                               SimContext* sim);

// §37.19: the member the var select `select`'s index names now -- an element
// of its array var, or of the subarray a var select it selects through names;
// null where an index on the way holds an x or z bit or lies outside its array
// (§11.5.1).
VpiObject* VpiVarSelectElement(const VpiObject& select, SimContext* sim);

}  // namespace delta
