#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.6.7 judges the data type of a nettype wherever the nettype is declared:
// in a package, in the compilation unit, in a procedural block and in a class,
// as among a module's own items.
::testing::AssertionResult NettypeReported(const std::string& src,
                                           uint32_t line) {
  ElabFixture f;
  Elaborate(src, f);
  return ReportedError(f.diag.Diagnostics(),
                       "data type of user-defined nettype 'n' is not a legal "
                       "nettype data type",
                       line, "6.6.7");
}

TEST(NettypeDataTypePlaces, PackageNettype) {
  EXPECT_TRUE(
      NettypeReported("package p;\n"
                      "  nettype string n;\n"
                      "endpackage\n"
                      "module m;\n"
                      "endmodule\n",
                      2));
  EXPECT_TRUE(
      NettypeReported("package p;\n"
                      "  nettype chandle n;\n"
                      "endpackage\n"
                      "module m;\n"
                      "endmodule\n",
                      2));
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  nettype real n;\n"
             "endpackage\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(NettypeDataTypePlaces, CompilationUnitNettype) {
  EXPECT_TRUE(
      NettypeReported("nettype string n;\n"
                      "module m;\n"
                      "endmodule\n",
                      1));
  EXPECT_TRUE(
      NettypeReported("typedef event e_t;\n"
                      "nettype e_t n;\n"
                      "module m;\n"
                      "endmodule\n",
                      2));
  EXPECT_TRUE(
      ElabOk("typedef struct { real r; bit b; } ok_t;\n"
             "nettype ok_t n;\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(NettypeDataTypePlaces, BlockAndClassNettype) {
  EXPECT_TRUE(
      NettypeReported("module m;\n"
                      "  initial begin\n"
                      "    nettype string n;\n"
                      "  end\n"
                      "endmodule\n",
                      3));
  EXPECT_TRUE(
      NettypeReported("module m;\n"
                      "  class C;\n"
                      "    nettype string n;\n"
                      "  endclass\n"
                      "endmodule\n",
                      3));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    nettype real n;\n"
             "  end\n"
             "endmodule\n"));
}

// A covergroup is a type of its own (§19.3), named by no item of the clause's
// list, whichever of these places names it.
TEST(NettypeDataTypePlaces, CovergroupNamedFromEachPlace) {
  EXPECT_TRUE(
      NettypeReported("package p;\n"
                      "  covergroup cg;\n"
                      "  endgroup\n"
                      "  nettype cg n;\n"
                      "endpackage\n"
                      "module m;\n"
                      "endmodule\n",
                      4));
  EXPECT_TRUE(
      NettypeReported("covergroup cg;\n"
                      "endgroup\n"
                      "nettype cg n;\n"
                      "module m;\n"
                      "endmodule\n",
                      3));
  EXPECT_TRUE(
      NettypeReported("module m;\n"
                      "  covergroup cg;\n"
                      "  endgroup\n"
                      "  initial begin\n"
                      "    nettype cg n;\n"
                      "  end\n"
                      "endmodule\n",
                      5));
}

}  // namespace
