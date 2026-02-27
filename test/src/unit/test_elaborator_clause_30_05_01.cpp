// §30.5.1: Specifying transition delays on module paths

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.4 Specify path delays — Elaboration
// =============================================================================
// 6-delay path elaborates
TEST(ElabA704, SixDelayPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// 12-delay path elaborates
TEST(ElabA704, TwelveDelayPathElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Min:typ:max delay elaborates
TEST(ElabA704, MinTypMaxDelayElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 1:2:3;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Min:typ:max with 2 delays elaborates
TEST(ElabA704, MinTypMaxTwoDelaysElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a => b) = (1:2:3, 4:5:6);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// 6-delay min:typ:max elaborates
TEST(ElabA704, SixDelayMinTypMaxElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  specify\n"
      "    (a *> b) = (1:2:3, 4:5:6, 7:8:9, 10:11:12, 13:14:15, 16:17:18);\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
