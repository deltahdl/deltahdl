// §35.7: Exported functions

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/dpi.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <cstdint>
#include <gtest/gtest.h>
#include <vector>

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

} // namespace
