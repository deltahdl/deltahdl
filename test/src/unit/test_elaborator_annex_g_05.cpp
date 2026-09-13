// IEEE 1800-2023 Annex G.5 (Std package -- Randomize).
//
// Section G.5 presents the prototype of the randomize function the std package
// provides, function int randomize( ... ), described in 18.12, and gives the
// form of a call of std::randomize as the randomize_call of A.8.2 applicable
// to it:
//
//   randomize { attribute_instance } [ ( [ variable_identifier_list ] ) ]
//       [ with constraint_block ]
//
// src/elaborator/std_package.h writes the prototype down, and the elaborator
// holds a call of std::randomize to that form: its arguments, any number of
// them, are variable identifiers. These tests observe the prototype, the
// accepted forms -- no list, an empty list, a list of variables, a with
// block -- and the rejection, at the argument and under §G.5, of an argument
// that is no variable identifier, where the same argument to the bare scope
// randomize of A.8.2 is rejected under that subclause.

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §G.5: function int randomize( ... ) -- a function returning int, taking
// any number of actuals, of the package and of no class.
TEST(RandomizeStdPackageElaborator, ThePrototypeIsWrittenDown) {
  const StdMethodPrototype& prototype = RandomizePrototype();
  EXPECT_EQ(prototype.name, "randomize");
  EXPECT_EQ(prototype.kind, StdMethodKind::kFunction);
  EXPECT_EQ(prototype.return_type, "int");
  EXPECT_TRUE(prototype.variadic);
  EXPECT_TRUE(prototype.formals.empty());
  EXPECT_FALSE(prototype.is_static);
  EXPECT_TRUE(StdClassPrototype(StdPackageMember::kRandomize).empty());
  EXPECT_EQ(KindOfStdPackageMember(StdPackageMember::kRandomize),
            StdPackageMemberKind::kFunction);
}

// §G.5: the forms the summary allows -- randomize with an empty list, with
// a list of variables, and with a constraint block -- each elaborate through
// std::randomize.
TEST(RandomizeStdPackageElaborator, TheFormsOfTheSummaryAreAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int a;\n"
             "  int b;\n"
             "  int ok;\n"
             "  initial begin\n"
             "    ok = std::randomize();\n"
             "    ok = std::randomize(a);\n"
             "    ok = std::randomize(a, b);\n"
             "    ok = std::randomize(a, b) with { a < b; };\n"
             "  end\n"
             "endmodule\n"));
}

// §G.5: the list is a variable_identifier_list, so an expression and a
// literal are rejected as arguments, at the argument and under §G.5 for
// std::randomize, while a variable beside them is accepted; the same
// arguments to the bare scope randomize are rejected under A.8.2, whose
// randomize_call gives the list.
TEST(RandomizeStdPackageElaborator, AnArgumentShallBeAVariableIdentifier) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int a;\n"
      "  int b;\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = std::randomize(a, b + 1);\n"
      "    ok = std::randomize(1);\n"
      "    ok = randomize(a + 1);\n"
      "    ok = std::randomize(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to std::randomize shall be a variable identifier", 6, "G.5"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to std::randomize shall be a variable identifier", 7, "G.5"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to a scope randomize call shall be a variable identifier", 8,
      "A.8.2"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, 9u);
  }
}

}  // namespace
