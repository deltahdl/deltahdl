#include <gtest/gtest.h>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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
