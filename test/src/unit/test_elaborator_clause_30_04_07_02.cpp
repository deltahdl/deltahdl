#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.4.7.2: elaborator accepts a positive-polarity parallel path.
TEST(PositivePolarityElaboration, ParallelPathWithPlusOperator) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a + => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.7.2: elaborator accepts a positive-polarity full path.
TEST(PositivePolarityElaboration, FullPathWithPlusOperator) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a + *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
