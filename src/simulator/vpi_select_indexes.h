#pragma once

#include <functional>

namespace delta {

struct Expr;
struct VpiObject;

void VpiNoteSelectIndexes(VpiObject* select, const Expr* expr,
                          const std::function<VpiObject*()>& alloc);

}  // namespace delta
