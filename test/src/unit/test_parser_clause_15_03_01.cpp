#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SemaphoreNewParser, NewWithExplicitKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    smTx = new(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreNewParser, NewWithNoArguments) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s;\n"
      "  initial begin\n"
      "    s = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreNewParser, DeclarationWithNewZeroKeys) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new(0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
