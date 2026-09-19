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
// src/elaborator/std_package.h writes the prototype down; the parser holds a
// call of std::randomize to that form, its arguments being variable
// identifiers (test_parser_annex_g_05.cpp), and the elaborator holds the bare
// scope form of A.8.2 to the same list where the parser lets a property name
// through. These tests observe the prototype, the accepted forms -- an empty
// list, a list of variables, a with block -- and the elaborator's rejection.

#include <gtest/gtest.h>

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

// §G.5 with §A.8.2: the list of a scope randomize call is a
// variable_identifier_list. The parser refuses an expression to any
// randomize call and, under §G.5, anything but a variable identifier to
// std::randomize; what it lets through to the bare scope form as a property
// name of §18.11, a member access and a select, the elaborator rejects under
// §A.8.2 at the argument, while a variable beside them is accepted.
TEST(RandomizeStdPackageElaborator, AScopeArgumentShallBeAVariableIdentifier) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  int a;\n"
      "  int arr [4];\n"
      "  int ok;\n"
      "  initial begin\n"
      "    ok = randomize(a, m.a);\n"
      "    ok = randomize(arr[0]);\n"
      "    ok = randomize(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to a scope randomize call shall be a variable identifier", 6,
      "A.8.2"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "argument to a scope randomize call shall be a variable identifier", 7,
      "A.8.2"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, 8u);
  }
}

}  // namespace
