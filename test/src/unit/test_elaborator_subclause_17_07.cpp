#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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

}  // namespace
