#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BoundedQueueElaboration, BoundedQueueDimension) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:255]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 256);
}

TEST(BoundedQueueElaboration, BoundOfOneIsValid) {
  ElabFixture f;
  auto* design = Elaborate("module m; int q [$:1]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 2);
}

// The rule on the bound's value belongs to §7.10, which states under Syntax
// 7-4 "constant_expression shall evaluate to a positive integer value";
// §7.10.5 states only how a bounded queue behaves once declared, so the report
// names §7.10.
TEST(BoundedQueueElaboration, BoundOfZeroIsError) {
  ElabFixture f;
  ElaborateSrc("module m; int q [$:0]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
}

// The report names §7.10 for the reason given above BoundOfZeroIsError.
TEST(BoundedQueueElaboration, NegativeBoundIsError) {
  ElabFixture f;
  ElaborateSrc("module m; int q [$:-1]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
}

// §7.10, Syntax 7-4: the bound in `[$:N]` "shall evaluate to a positive
// integer value", and the subclause puts no scope on that, so a declaration
// inside a procedural block is held to it as a module item's declaration is.
// The report names §7.10 for the reason given above BoundOfZeroIsError.
TEST(BoundedQueueElaboration, BlockScopedBoundOfZeroIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int q[$:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 3,
                            "7.10"));
}

}  // namespace
