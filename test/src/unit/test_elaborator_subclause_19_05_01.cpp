#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RealCoverpointDefaultBin, DefaultBinArrayOfRealCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  covergroup cg;\n"
      "    a: coverpoint r { bins lo = {[0.0:1.0]}; bins d[] = default; }\n"
      "    b: coverpoint r { bins lo = {[0.0:1.0]}; bins e[4] = default; }\n"
      "    c: coverpoint r { bins lo = {[0.0:1.0]}; bins g = default; }\n"
      "    d: coverpoint i { bins h[] = default; }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a real coverpoint's default bin is a single bin "
                              "and cannot be declared as an array",
                              line, "19.5.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(FixedBinCount, ConstantCountOfZeroOrLessIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] v;\n"
      "  covergroup cg;\n"
      "    coverpoint v {\n"
      "      bins z[0] = {[0:7]};\n"
      "      bins n[-2] = {[8:15]};\n"
      "      bins one[1] = {[0:15]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bins 'z' asks for 0 bins; the number of bins is a "
                            "positive integral value",
                            5, "19.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bins 'n' asks for -2 bins; the number of bins is "
                            "a positive integral value",
                            6, "19.5.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(FixedBinCount, DISABLED_ANonIntegralCountIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] v; real r;\n"
      "  parameter real K = 2.5;\n"
      "  covergroup cg;\n"
      "    coverpoint v { bins a[2.5] = {[0:7]}; bins b[K] = {[8:15]}; }\n"
      "    coverpoint r { bins a[2.5] = {[0.0:4.0]}; bins b[K] = {[4.0:8.0]}; "
      "}\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    for (const char* name : {"a", "b"}) {
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                std::string("the number of bins of bins '") +
                                    name + "' is not integral",
                                line, "19.5.1"))
          << line << " " << name;
    }
  }
}

TEST(FixedBinCount, AnIntegralCountOfAnyIntegralTypeIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] v; real r;\n"
      "  parameter byte K = 3;\n"
      "  covergroup cg;\n"
      "    coverpoint v { bins a[3] = {[0:7]}; bins b[K] = {[8:15]}; }\n"
      "    coverpoint r { bins a[4'd3] = {[0.0:4.0]}; bins b[K] = {[4.0:8.0]}; "
      "}\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
