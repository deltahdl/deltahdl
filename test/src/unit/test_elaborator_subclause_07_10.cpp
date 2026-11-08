#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(QueueDeclarationElaboration, UnboundedQueueDimension) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, -1);
}

TEST(QueueDeclarationElaboration, BoundedQueueDimensionRecordsCapacity) {
  ElabFixture f;
  auto* design = Elaborate("module m; bit b [$:7]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 8);
}

TEST(QueueDeclarationElaboration, NonPositiveBoundEmitsError) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:-1]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
}

TEST(QueueDeclarationElaboration, LocalparamBoundRecordsCapacity) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int N = 7;\n"
      "  bit b [$:N];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const RtlirVariable* q = nullptr;
  for (auto& v : mod->variables)
    if (v.name == "b") q = &v;
  ASSERT_NE(q, nullptr);
  EXPECT_TRUE(q->is_queue);
  EXPECT_EQ(q->queue_max_size, 8);
}

TEST(QueueDeclarationElaboration, ParameterNonPositiveBoundEmitsError) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int N = 0;\n"
      "  int q [$:N];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 3,
                            "7.10"));
}

TEST(QueueDeclarationElaboration, BoundInsideGenerateBlocksIsChecked) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic y;", "initial begin int q[$:-1]; end"},
      "queue bound must be a positive integer", "7.10"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "logic y;", "initial begin int q[$:1]; end"}));
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  for (genvar i = 0; i < 2; i++) begin : g\n"
        "    initial begin int q[$:i]; end\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "queue bound must be a positive integer", 3,
                              "7.10"));
  }
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  for (genvar i = 1; i < 3; i++) begin : g\n"
             "    initial begin int q[$:i]; end\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
