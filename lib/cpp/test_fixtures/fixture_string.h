#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "helpers_method_call.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"

using namespace delta;

struct StringFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  Variable* CreateStringVar(std::string_view var_name, std::string_view value) {
    uint32_t width = static_cast<uint32_t>(value.size()) * 8;
    if (width == 0) width = 8;
    auto* var = ctx.CreateVariable(var_name, width);
    var->value = MakeLogic4Vec(arena, width);
    for (size_t i = 0; i < value.size(); ++i) {
      auto byte_idx = static_cast<uint32_t>(value.size() - 1 - i);
      uint32_t word = (byte_idx * 8) / 64;
      uint32_t bit = (byte_idx * 8) % 64;
      var->value.words[word].aval |=
          static_cast<uint64_t>(static_cast<unsigned char>(value[i])) << bit;
    }
    ctx.RegisterStringVariable(var_name);
    return var;
  }

  Expr* MakeMethodCall(std::string_view var_name, std::string_view method_name,
                       std::vector<Expr*> args = {}) {
    return MakeMethodCallExpr(arena, var_name, method_name, std::move(args));
  }

  Expr* MakeIntLiteral(uint64_t val) {
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }
};
