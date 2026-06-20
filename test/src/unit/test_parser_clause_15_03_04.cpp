#include "fixture_parser.h"

using namespace delta;

namespace {

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
