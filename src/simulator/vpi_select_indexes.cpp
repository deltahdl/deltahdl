#include "simulator/vpi_select_indexes.h"

#include <functional>
#include <initializer_list>

#include "parser/ast_expr.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"

namespace delta {

void VpiNoteSelectIndexes(VpiObject* select, const Expr* expr,
                          const std::function<VpiObject*()>& alloc) {
  // A select written with no base, as an inside set's range `[2:3]` is,
  // ends the walk as one written over a name does.
  for (const Expr* at = expr; at != nullptr && at->kind == ExprKind::kSelect;
       at = at->base) {
    for (const Expr* index : {at->index, at->index_end}) {
      if (!VpiSourceExprHasSideEffects(index)) continue;
      VpiObject* marked = alloc();
      marked->has_side_effects = true;
      select->index_expressions.push_back(marked);
    }
  }
}

}  // namespace delta
