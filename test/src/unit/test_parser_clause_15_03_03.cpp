#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SemaphoreGetParser, GetWithExplicitKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get(2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreGetParser, GetWithDefaultKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.get();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreGetParser, GetOnDeclaredSemaphore) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s = new(3);\n"
      "  initial begin\n"
      "    s.get(1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphoreGetParser, GetUsedAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s;\n"
      "  initial begin\n"
      "    s.get();\n"
      "    s.get(5);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
