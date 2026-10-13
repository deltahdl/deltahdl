#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// §17.7: variables may be defined in a checker, but defining nets in the
// checker body is illegal.
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

// §17.7: ordinary (deterministic) checker variables are legal in a checker
// body and define checker variables, not nets.
TEST(CheckerVariables, VariableDeclaredInCheckerBodyIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  bit [2:0] counter = '0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

// §17.7: checker variables may carry the rand qualifier, making them free
// variables. Such declarations are the [ rand ] data_declaration of §17.2's
// checker_or_generate_item_declaration and must elaborate cleanly.
TEST(CheckerVariables, RandFreeVariableInCheckerBodyIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(bit valid);\n"
      "  rand bit flag;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

// §17.7: a free checker variable declaration may additionally carry a const
// qualifier, producing a constant free variable. Such a declaration elaborates
// cleanly as a checker variable.
TEST(CheckerVariables, ConstFreeVariableInCheckerBodyIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(bit valid);\n"
      "  rand const bit [5:0] idx;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

// §17.7: a constant free checker variable may be initialized in its
// declaration, retaining that value; the initializer elaborates as a checker
// variable initialization.
TEST(CheckerVariables, ConstFreeVariableWithInitializerIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(bit valid);\n"
      "  rand const bit [3:0] k = 4'd7;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

// §17.7.2: of a checker's free variables, a `const` one and one a checker
// variable assignment writes, by name, element, member or concatenation, are
// inactive, and each without an initializer takes a random initial value.
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
