// §35.5: Imported tasks and functions

#include <gtest/gtest.h>
#include <cstdint>
#include <vector>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/dpi.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

// =============================================================================
// DpiContext registration
// =============================================================================
TEST(Dpi, RegisterImport) {
  DpiContext ctx;
  DpiFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] + args[1];
  };
  ctx.RegisterImport(func);

  EXPECT_EQ(ctx.ImportCount(), 1u);
  EXPECT_TRUE(ctx.HasImport("sv_add"));
  EXPECT_FALSE(ctx.HasImport("nonexistent"));
}

TEST(Dpi, FindImport) {
  DpiContext ctx;
  DpiFunction func;
  func.c_name = "c_mul";
  func.sv_name = "sv_mul";
  func.return_type = DataTypeKind::kInt;
  ctx.RegisterImport(func);

  const auto* found = ctx.FindImport("sv_mul");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->c_name, "c_mul");

  EXPECT_EQ(ctx.FindImport("missing"), nullptr);
}

}  // namespace
