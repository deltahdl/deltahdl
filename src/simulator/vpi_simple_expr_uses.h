#pragma once

#include <vector>

#include "simulator/vpi_object.h"

namespace delta {

// §37.58 (figure): whether `obj` is a simple expression, the kinds whose
// vpiUse relation reaches the objects that use them: a net, a variable, a ref
// obj, a parameter, a spec param, a var select or a bit select.
bool VpiIsSimpleExpr(VpiHandle obj);

// §37.58 details 1 and 2: whether the expression `node`, or one written inside
// it, uses `expr`. Of a vector, the vector or any select of it is a use; of a
// bit, that bit, the vector it is a bit of, or a select of that vector holding
// it.
bool VpiExpressionUses(const VpiObject* node, const VpiObject& expr);

// §37.58 details 1 and 2: whether `use`, an object an expression is written
// with, uses `expr` through one of its two sides, one of the two ends of a
// port, or an expression it holds. Of a vector, a use of the vector or of any
// select of it counts; of a bit, a use of that bit, of the vector it is a bit
// of, or of a select of that vector holding it.
bool VpiUsesExpr(const VpiObject& use, const VpiObject& expr);

// §37.58 details 1 and 2: the objects the vpiUse relation of the simple
// expression `expr` reaches, in the order the design holds them. Each is a
// prim term, path term, tchk term, delay term, port, statement, cont assign or
// cont assign bit whose own expressions use `expr`. Of a vector, a use of the
// vector or of any select of it counts; of a bit, a use of that bit, of the
// vector it is a bit of, or of a part select of that vector holding it.
std::vector<VpiObject*> VpiSimpleExprUses(VpiHandle expr);

}  // namespace delta
