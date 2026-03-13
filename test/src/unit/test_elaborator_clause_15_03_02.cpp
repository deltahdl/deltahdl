#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.3.2: put() call in initial block elaborates without error.
TEST(SemaphorePutElaborator, PutCallInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem.put(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3.2: put() with default keyCount elaborates.
TEST(SemaphorePutElaborator, PutDefaultKeyCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem.put();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3.2: multiple put() calls elaborate.
TEST(SemaphorePutElaborator, MultiplePutCalls) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore s;\n"
      "  initial begin\n"
      "    s.put(1);\n"
      "    s.put(2);\n"
      "    s.put();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
