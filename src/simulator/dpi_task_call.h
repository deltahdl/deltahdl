#ifndef DELTA_SIMULATOR_DPI_TASK_CALL_H_
#define DELTA_SIMULATOR_DPI_TASK_CALL_H_

#include <string_view>
#include <vector>

#include "common/arena.h"
#include "parser/ast_expr.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/exec_task.h"
#include "simulator/sim_context.h"

namespace delta {

// §35.2.1: whether the call statement `expr` enables an imported task.
bool EnablesDpiImportTask(const Expr* expr, SimContext& ctx);

// §35.8 with §35.5.1.5: runs the imported task `expr` enables. Its foreign
// function runs on a thread of its own while the enabling process waits, so
// that an exported task it calls can consume time: the C code's thread waits
// in that call while this process runs the task's body, time passing and other
// processes running as it does, and resumes once the body ends. The two
// threads take turns, never running at once. A disable that ends the body
// returns 1 from the exported task to the C code and leaves it in the disabled
// state (§35.9), and the enable then ends as a disabled one.
ExecTask ExecDpiImportTask(const Expr* expr, SimContext& ctx, Arena& arena);

// §35.8: an exported task's implementation, called from the C code of an
// imported task: hands the task, keyed `key`, and `args` to the process that
// enabled the import and waits until it has run the task, its outputs then in
// `args`. Called from any other thread it runs nothing.
DpiArgValue RunExportedTaskFromC(const DpiRtExport& exp, std::string_view key,
                                 std::vector<DpiArgValue>& args);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_TASK_CALL_H_
