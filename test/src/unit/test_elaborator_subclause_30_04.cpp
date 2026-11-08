#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ModulePathDeclElaboration, FullConnectionMixesScalarSourceAndVectorDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input s, output [7:0] q);\n"
      "  specify\n"
      "    (s *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModulePathDeclElaboration, FullConnectionVectorSourceToVectorDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output [7:0] q);\n"
      "  specify\n"
      "    (a *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModulePathDeclElaboration, FullConnectionVectorSourceToScalarDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input [7:0] a, output q);\n"
      "  specify\n"
      "    (a *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModulePathDeclElaboration, FullConnectionScalarSourceToScalarDest) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, output q);\n"
      "  specify\n"
      "    (a *> q) = 1;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModulePathDeclElaboration, MultipleSourcesToSameDestination) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input a, input b, output q);\n"
      "  specify\n"
      "    (a => q) = 10;\n"
      "    (b => q) = 12;\n"
      "  endspecify\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
