#include "fixture_parser.h"

using namespace delta;

namespace {

// §15.3.2: put() with explicit keyCount parses.
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

// §15.3.2: put() with no arguments (default keyCount = 1).
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

// §15.3.2: put() called on a declared semaphore variable.
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

// §15.3.2: multiple put() calls in sequence.
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
