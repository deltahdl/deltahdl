#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.3.1: new() with explicit key count parses in assignment.
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

// §15.3.1: new() with no arguments (default keyCount = 0).
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

// §15.3.1: new() in declaration initializer with zero keys.
TEST(SemaphoreNewParser, DeclarationWithNewZeroKeys) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new(0);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.3.1: new() with large key count.
TEST(SemaphoreNewParser, DeclarationWithLargeKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  semaphore sem = new(100);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.3.1: new() returns the semaphore handle — variable stores it.
TEST(SemaphoreNewParser, NewReturnAssignedToVariable) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s1;\n"
      "  semaphore s2;\n"
      "  initial begin\n"
      "    s1 = new(3);\n"
      "    s2 = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
