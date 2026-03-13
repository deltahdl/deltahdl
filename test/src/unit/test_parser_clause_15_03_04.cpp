#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.3.4: try_get() with explicit keyCount parses.
TEST(SemaphoreTryGetParser, TryGetWithExplicitKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.try_get(2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.3.4: try_get() with no arguments (default keyCount = 1).
TEST(SemaphoreTryGetParser, TryGetWithDefaultKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.try_get();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.3.4: try_get() on a declared semaphore variable.
TEST(SemaphoreTryGetParser, TryGetOnDeclaredSemaphore) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s = new(3);\n"
      "  initial begin\n"
      "    s.try_get(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.3.4: try_get() used in an expression context (returns int).
TEST(SemaphoreTryGetParser, TryGetUsedInExpression) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = s.try_get(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
