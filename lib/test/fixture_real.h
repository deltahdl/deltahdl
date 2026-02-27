#pragma once

#include <cstring>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"

using namespace delta;

inline double VecToDouble(const Logic4Vec& vec) {
  uint64_t bits = vec.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

struct RealFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  Expr* MakeRealLiteral(double val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kRealLiteral;
    lit->real_val = val;
    return lit;
  }

  Expr* MakeIntLiteral(uint64_t val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }

  Variable* CreateRealVar(std::string_view name, double val) {
    auto* var = ctx.CreateVariable(name, 64);
    uint64_t bits = 0;
    std::memcpy(&bits, &val, sizeof(double));
    var->value = MakeLogic4VecVal(arena, 64, bits);
    ctx.RegisterRealVariable(name);
    return var;
  }
};
