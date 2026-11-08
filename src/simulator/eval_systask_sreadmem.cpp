#include <cstddef>
#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/eval_systask_readmem_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

Logic4Vec EvalSreadmem(const Expr* expr, SimContext& ctx, Arena& arena,
                       bool is_hex) {
  if (expr->args.size() < 4) {
    ctx.GetDiag().Error(expr->range.start,
                        std::string(is_hex ? "$sreadmemh" : "$sreadmemb") +
                            " takes a memory name, a start address, a finish "
                            "address, and one or more strings, and this call "
                            "has fewer",
                        Subclause("D.14"));
    return MakeLogic4VecVal(arena, 1, 0);
  }
  int64_t start_arg =
      static_cast<int64_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  int64_t finish_arg =
      static_cast<int64_t>(EvalExpr(expr->args[2], ctx, arena).ToUint64());

  std::string content;
  for (size_t i = 3; i < expr->args.size(); ++i) {
    if (i > 3) content += '\n';
    content += EvalStringArg(expr->args[i], ctx, arena);
  }

  ReadmemEnv env{ctx, arena, is_hex, expr->range.start};
  DoMemLoad(env, content, expr->args[0], {true, true, start_arg, finish_arg});
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
