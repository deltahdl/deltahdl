#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InstantiationFormElaboration, ACheckerTakesNoParameterValueAssignment) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  chk #(.W(4)) c1(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "checker 'chk' cannot be instantiated with a parameter value assignment",
      5, "A.4.1.4"));
}

TEST(InstantiationFormElaboration, AnOrderedAssignmentOnACheckerIsRefusedToo) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  chk #(4) c1(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "checker 'chk' cannot be instantiated with a parameter value assignment",
      5, "A.4.1.4"));
}

TEST(InstantiationFormElaboration, AnEmptyAssignmentOnACheckerIsRefusedToo) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  chk #() c1(s);\n"
      "  initial begin\n"
      "    chk #() c2(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMsg =
      "checker 'chk' cannot be instantiated with a parameter value assignment";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMsg, 5, "A.4.1.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMsg, 7, "A.4.1.4"));
}

TEST(InstantiationFormElaboration, ACheckerWithoutOneElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s;\n"
      "  chk c1(s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InstantiationFormElaboration, TheOtherThreeFormsTakeTheAssignment) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ifc #(parameter W = 1) ();\n"
      "endinterface\n"
      "program prg #(parameter W = 1) ();\n"
      "endprogram\n"
      "module sub #(parameter W = 1) ();\n"
      "endmodule\n"
      "module m;\n"
      "  ifc #(.W(4)) i1();\n"
      "  prg #(.W(4)) p1();\n"
      "  sub #(.W(4)) s1();\n"
      "  ifc #() i2();\n"
      "  prg #() p2();\n"
      "  sub #() s2();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InstantiationFormElaboration, ACheckerTakesOneInstancePerInstantiation) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a);\n"
      "endchecker\n"
      "module m;\n"
      "  logic s, t;\n"
      "  chk c1(s), c2(t);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker 'chk' is instantiated one instance to an "
                            "instantiation; 'c2' after a ',' is a second",
                            5, "A.4.1.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'c1' after a ',' is a second", 5, "A.4.1.4"));
}

TEST(InstantiationFormElaboration, TheOtherThreeFormsTakeTheInstanceList) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface ifc ();\n"
      "endinterface\n"
      "program prg ();\n"
      "endprogram\n"
      "module sub ();\n"
      "endmodule\n"
      "module m;\n"
      "  ifc i1(), i2();\n"
      "  prg p1(), p2();\n"
      "  sub s1(), s2();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
