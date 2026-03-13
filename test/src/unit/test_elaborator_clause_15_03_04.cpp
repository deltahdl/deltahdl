#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.3.4: try_get() call in initial block elaborates without error.
TEST(SemaphoreTryGetElaborator, TryGetCallInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem.try_get(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3.4: try_get() with default keyCount elaborates.
TEST(SemaphoreTryGetElaborator, TryGetDefaultKeyCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem;\n"
      "  initial begin\n"
      "    sem.try_get();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3.4: try_get() result assigned to variable elaborates.
TEST(SemaphoreTryGetElaborator, TryGetResultAssigned) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = s.try_get(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
