#pragma once

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

// §12.6.2/§12.6.3: a `matches ... &&& <side-effect>` predicate is a sequential
// conjunction evaluated left to right; once the matches clause fails, the
// side-effecting clause to its right must not run. `pred_stmt` is the single
// procedural statement (an if-matches or a ternary-matches assignment) whose
// matches clause fails, so `cnt` must stay 0 and `y` must take the else
// value 2.
inline void RunMatchesShortCircuitSkipsLaterClause(
    const std::string& pred_stmt) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y, cnt;\n"
      "  initial begin\n"
      "    x = 8'd5;\n"
      "    cnt = 8'd0;\n"
      "    y = 8'd0;\n"
      "    " +
          pred_stmt +
          "\n"
          "  end\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* cnt = f.ctx.FindVariable("cnt");
  ASSERT_NE(cnt, nullptr);
  EXPECT_EQ(cnt->value.ToUint64(), 0u);
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 2u);
}
