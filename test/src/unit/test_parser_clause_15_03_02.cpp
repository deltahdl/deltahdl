#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SemaphorePutParser, PutWithExplicitKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.put(3);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphorePutParser, PutWithDefaultKeyCount) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.put();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphorePutParser, PutOnDeclaredSemaphore) {
  auto r = Parse(
      "module m;\n"
      "  semaphore s = new(0);\n"
      "  initial begin\n"
      "    s.put(5);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(SemaphorePutParser, MultiplePutCalls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sem.put(1);\n"
      "    sem.put(2);\n"
      "    sem.put();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
