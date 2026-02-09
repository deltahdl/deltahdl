#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "simulation/dpi.h"

using namespace delta;

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

TEST(Dpi, CallFunction) {
  DpiContext ctx;
  DpiFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] + args[1];
  };
  ctx.RegisterImport(func);

  auto result = ctx.Call("sv_add", {10, 20});
  EXPECT_EQ(result, 30u);
}

TEST(Dpi, CallMissingReturnsZero) {
  DpiContext ctx;
  auto result = ctx.Call("nonexistent", {1, 2});
  EXPECT_EQ(result, 0u);
}

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
