#include "elaborator/subroutine_instance_copy.h"

#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/global_clock_assertion_event.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

ModuleItem* WithGlobalClockSubstituted(
    ModuleItem* item, const std::vector<EventExpr>* global_event,
    Arena& arena) {
  if (global_event == nullptr) return item;
  std::vector<Stmt*> body;
  bool rewritten = false;
  for (Stmt* s : item->func_body_stmts) {
    Stmt* substituted =
        SubstituteGlobalClockEventControls(s, *global_event, arena);
    rewritten |= substituted != s;
    body.push_back(substituted);
  }
  if (!rewritten) return item;
  auto* copy = arena.Create<ModuleItem>(*item);
  copy->func_body_stmts = std::move(body);
  return copy;
}

}  // namespace delta
