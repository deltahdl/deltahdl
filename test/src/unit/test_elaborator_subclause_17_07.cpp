#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(CheckerVariables, NetDeclaredInCheckerBodyIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  wire w;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a net cannot be declared inside checker", 2,
                            "17.7"));
}

TEST(CheckerVariables, VariableDeclaredInCheckerBodyIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit [2:0] counter = '0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariables, RandFreeVariableInCheckerBodyIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(bit valid);\n"
      "  rand bit flag;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariables, ConstFreeVariableInCheckerBodyIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(bit valid);\n"
      "  rand const bit [5:0] idx;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariables, ConstFreeVariableWithInitializerIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(bit valid);\n"
      "  rand const bit [3:0] k = 4'd7;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerVariables, FreeVariablesSplitIntoActiveAndRandomlyInitialized) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(logic clk);\n"
      "  typedef struct packed { bit x; bit y; } pair_t;\n"
      "  rand bit a, b, c, d, e;\n"
      "  rand bit g = 1'b1;\n"
      "  rand const bit k;\n"
      "  rand bit [1:0] s;\n"
      "  rand pair_t p;\n"
      "  always_ff @(posedge clk) a <= !a;\n"
      "  always_ff @(posedge clk) s[0] <= 1'b1;\n"
      "  always_ff @(posedge clk) p.x <= 1'b1;\n"
      "  always_comb {b, c} = 2'b01;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  const RtlirModule* mod = design->top_modules[0];
  EXPECT_EQ(mod->free_variables,
            (std::vector<std::string_view>{"d", "e", "g"}));
  EXPECT_EQ(
      mod->random_initial_variables,
      (std::vector<std::string_view>{"a", "b", "c", "d", "e", "k", "s", "p"}));
}

}  // namespace
