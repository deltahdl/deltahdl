// §26.3: Referencing data in packages

#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.9: "Package declarations can be imported into other building blocks,
//        including other packages."
TEST(ParserClause03, Cl3_9_ImportIntoModuleAndPackage) {
  auto r = ParseWithPreprocessor(
      "package A; typedef int myint; endpackage\n"
      "package B; import A::*; endpackage\n"
      "module m; import A::myint; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  EXPECT_EQ(r.cu->packages[0]->name, "A");
  EXPECT_EQ(r.cu->packages[1]->name, "B");
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
