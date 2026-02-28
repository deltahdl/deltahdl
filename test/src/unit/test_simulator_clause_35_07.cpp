// §35.7: Exported functions

#include <cstdint>
#include <vector>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(Dpi, RegisterExport) {
  DpiContext ctx;
  DpiExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  ctx.RegisterExport(exp);

  EXPECT_EQ(ctx.ExportCount(), 1u);
  EXPECT_TRUE(ctx.HasExport("sv_callback"));
  EXPECT_FALSE(ctx.HasExport("missing"));
}

}  // namespace
