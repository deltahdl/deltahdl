#include "fixture_simulator.h"
#include "helpers_clocking.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(StringConcatAndReplication, StringConcatElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string a, b, c;\n"
      "  initial begin\n"
      "    a = \"hello\";\n"
      "    b = \" world\";\n"
      "    c = {a, b};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringReplicationElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {3{\"ab\"}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, NonConstantMultiplierAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    int n;\n"
      "    string s;\n"
      "    n = 3;\n"
      "    s = {n{\"boo \"}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatWithLiteralElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial s = {\"hello\", \" \", \"world\"};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatAppendElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"hello\";\n"
      "    s = {s, \" world\"};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatOnLhsBlockingAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatOnLhsNonblockingAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  initial {a, b} <= \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(StringConcatAndReplication, StringConcatOnLhsContAssignRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  string a, b;\n"
      "  assign {a, b} = \"hello\";\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(StringConcatAndReplication, BitConcatOnLhsStillAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial {a, b} = 8'hC3;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
