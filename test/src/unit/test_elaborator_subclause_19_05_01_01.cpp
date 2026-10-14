#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.5.1.1: a `with` expression filters the values of a bin, and is not
// allowed for the bins of a real coverpoint, whether it follows a range list
// or the coverpoint's own name. An integral coverpoint's bin may take one.
TEST(RealCoverpointBinWith, WithOnRealCoverpointBinIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  covergroup cg;\n"
      "    a: coverpoint r { bins b[] = {[1.0:4.0]} with (item > 2.0); }\n"
      "    c: coverpoint r { bins d = c with (item > 2.0); }\n"
      "    e: coverpoint i { bins g[] = {[1:4]} with (item > 2); }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a bin of a real coverpoint takes no 'with' "
                              "expression",
                              line, "19.5.1.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §19.5.1.1: only the coverpoint holding a bin may be named in place of its
// range list, so naming another coverpoint of the covergroup is an error.
TEST(CoverpointBinWith, NamingAnotherCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] x, y;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y {\n"
      "      bins odd[] = a with (item % 2 == 1);\n"
      "      bins even[] = b with (item % 2 == 0);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bin 'odd' names coverpoint 'a' before 'with'; "
                            "only the coverpoint holding the bin may stand "
                            "there",
                            6, "19.5.1.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

// Footnote 31 of Syntax 19-2 with §19.5.1.1: a bin's `with` expression is
// assignment compatible with an integral type, which a string and a class
// handle are not; a comparison over `item` is.
TEST(CoverpointBinWith, WithExpressionNotIntegralIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  bit [3:0] v;\n"
      "  function automatic string fs(); return \"a\"; endfunction\n"
      "  function automatic C fh(); return null; endfunction\n"
      "  covergroup cg;\n"
      "    coverpoint v {\n"
      "      bins c[] = {[0:15]} with (fs());\n"
      "      bins d[] = {[0:15]} with (fh());\n"
      "      bins e[] = {[0:15]} with (item > 3);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the 'with' expression of bin 'c' is not "
                            "assignment compatible with an integral type",
                            8, "19.5.1.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the 'with' expression of bin 'd' is not "
                            "assignment compatible with an integral type",
                            9, "19.5.1.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
