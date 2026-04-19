#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §30.4.7.3: elaborator accepts a negative-polarity parallel path.
TEST(NegativePolarityElaboration, ParallelPathWithMinusOperator) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a - => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §30.4.7.3: elaborator accepts a negative-polarity full path.
TEST(NegativePolarityElaboration, FullPathWithMinusOperator) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a - *> b) = 5;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
