#include "elaborator/subroutine_instance_copy.h"

#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/global_clock_assertion_event.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

// §14.14 (printed pages 363-366): `$global_clock` names the global clocking
// event of the scope it is written in, a subroutine's body among them, so an
// event control naming it in a task, `@($global_clock)`, waits on the event of
// the declaration effective where the task is declared -- the substitution a
// process body takes (BuildProcessBody in elaborator_process.cpp). Left as it
// was, the event control evaluated `$global_clock` as a call and the run
// reported no such system function. The rewrite is made on a copy of the
// declaration, as a process's is, because the one declaration the parser built
// serves every instance of the module; the declaration itself is kept where
// its body names no `$global_clock`.
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
