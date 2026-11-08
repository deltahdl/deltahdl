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

bool EnablesDpiImportTask(const Expr* expr, SimContext& ctx);

ExecTask ExecDpiImportTask(const Expr* expr, SimContext& ctx, Arena& arena);

DpiArgValue RunExportedTaskFromC(const DpiRtExport& exp, std::string_view key,
                                 std::vector<DpiArgValue>& args);

}  // namespace delta

#endif
