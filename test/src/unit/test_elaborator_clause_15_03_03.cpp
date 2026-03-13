#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.3.3: get() call in initial block elaborates without error.
TEST(SemaphoreGetElaborator, GetCallInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem.get(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3.3: get() with default keyCount elaborates.
TEST(SemaphoreGetElaborator, GetDefaultKeyCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem.get();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3.3: multiple get() calls elaborate.
TEST(SemaphoreGetElaborator, MultipleGetCalls) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore s;\n"
      "  initial begin\n"
      "    s.get(1);\n"
      "    s.get(2);\n"
      "    s.get();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
