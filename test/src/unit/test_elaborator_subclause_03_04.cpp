#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(DesignElementPlacement, ModuleInstanceInAProgramGenerateBlock) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  if (1) begin : g\n"
      "    sub u0();\n"
      "  end\n"
      "endprogram\n"
      "module sub; endmodule\n"
      "module top; p pi(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instantiations not allowed in programs", 3,
                            "24.3"));
}

TEST(DesignElementPlacement, UdpInstanceInAProgramGenerateBlock) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  for (genvar k = 0; k < 1; k = k + 1) begin : g\n"
      "    inv u1(a, b);\n"
      "  end\n"
      "endprogram\n"
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; p pi(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive cannot be instantiated inside program "
                            "'p'",
                            3, "24.3"));
}

TEST(DesignElementPlacement, ModuleInstanceInACheckerGenerateBlock) {
  ElabFixture f;
  ElaborateSrc(
      "checker c;\n"
      "  if (1) begin : g\n"
      "    m u();\n"
      "  end\n"
      "endchecker\n"
      "module m; endmodule\n"
      "module top; c ci(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "only checkers can be instantiated inside checker "
                            "'c'",
                            3, "17.2"));
}

TEST(DesignElementPlacement, ModuleInstanceInAnInterfaceGenerateCase) {
  ElabFixture f;
  ElaborateSrc(
      "interface i;\n"
      "  case (1)\n"
      "    1: begin : g\n"
      "      m u();\n"
      "    end\n"
      "  endcase\n"
      "endinterface\n"
      "module m; endmodule\n"
      "module top; i ii(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'm' cannot be instantiated inside "
                            "interface 'i'",
                            4, "25.3"));
}

TEST(DesignElementPlacement, EarlierUdpInstanceInACheckerGenerateBlock) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "checker c;\n"
      "  if (1) begin : g\n"
      "    inv u1(a, b);\n"
      "  end\n"
      "endchecker\n"
      "module top; c ci(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive cannot be instantiated inside checker "
                            "'c'",
                            6, "A.1.8"));
}

}  // namespace
