// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ComplexPkgExample) {
  auto r = Parse(
      "package ComplexPkg;\n"
      "  typedef struct {\n"
      "    shortreal i, r;\n"
      "  } Complex;\n"
      "  function Complex add(Complex a, b);\n"
      "    add.r = a.r + b.r;\n"
      "    add.i = a.i + b.i;\n"
      "  endfunction\n"
      "  function Complex mul(Complex a, b);\n"
      "    mul.r = (a.r * b.r) - (a.i * b.i);\n"
      "    mul.i = (a.r * b.i) + (a.i * b.r);\n"
      "  endfunction\n"
      "endpackage : ComplexPkg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "ComplexPkg");
}

TEST(DesignBuildingBlockParsing, LocalScopesDoNotConflict) {
  EXPECT_TRUE(
      ParseOk("module a; logic x; endmodule\n"
              "module b; logic x; endmodule\n"));
}

}  // namespace
