#include <gtest/gtest.h>

#include <string>

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

TEST(BoundedQueueElaboration, BoundOfZeroIsError) {
  ElabFixture f;
  ElaborateSrc("module m; int q [$:0]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
}

TEST(BoundedQueueElaboration, NegativeBoundIsError) {
  ElabFixture f;
  ElaborateSrc("module m; int q [$:-1]; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer", 1,
                            "7.10"));
}

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

void ExpectBlockQueueBoundErrorIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  logic ok;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "queue bound must be a positive integer",
                            LineHolding(src, "int q[$:0];"), "7.10"));
}

TEST(BoundedQueueElaboration, BoundOfZeroInAnAssertionPassStmt) {
  ExpectBlockQueueBoundErrorIn("assert (ok) begin int q[$:0]; end");
}

TEST(BoundedQueueElaboration, BoundOfZeroInAnAssertionFailStmt) {
  ExpectBlockQueueBoundErrorIn("assert (ok) else begin int q[$:0]; end");
}

TEST(BoundedQueueElaboration, BoundOfZeroInARandcaseItem) {
  ExpectBlockQueueBoundErrorIn("randcase 1: begin int q[$:0]; end endcase");
}

TEST(BoundedQueueElaboration, BoundOfZeroInARandsequenceCodeBlock) {
  ExpectBlockQueueBoundErrorIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { int q[$:0]; };\n"
      "      endsequence\n"
      "    end");
}

TEST(BoundedQueueElaboration, BoundOfZeroInARandsequenceWeightCodeBlock) {
  ExpectBlockQueueBoundErrorIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { int q[$:0]; };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
