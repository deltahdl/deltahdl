#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kProgramSignalRef =
    "hierarchical reference to program signal from outside the program is not "
    "permitted";

TEST(ProgramSignalReference, DisplayArgumentFromTheModuleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "  initial $display(\"%0d\", pi.v);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 6, "24.3"));
}

TEST(ProgramSignalReference, ReturnedValueInAModuleFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "  function int peek();\n"
      "    return pi.v;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 7, "24.3"));
}

TEST(ProgramSignalReference, PathThroughTheDesignFromAnotherModuleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "module mon;\n"
      "  initial $display(\"%0d\", top.pi.v);\n"
      "endmodule\n"
      "module top;\n"
      "  p pi();\n"
      "  mon m();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 5, "24.3"));
}

TEST(ProgramSignalReference, PathFromAnotherProgramIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "program r;\n"
      "  initial $display(\"%0d\", top.pi.v);\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "  r ri();\n"
      "endmodule\n",
      f, "top");
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 5, "24.3"));
}

TEST(AnonymousProgramHierRef, PathReachingAProgramInstanceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program q; int v = 3; endprogram\n"
      "program;\n"
      "  function int peek(); return top.qi.v; endfunction\n"
      "endprogram\n"
      "program p;\n"
      "  initial $display(\"%0d\", peek());\n"
      "endprogram\n"
      "module top; q qi(); p pi(); endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 3, "24.3"));
}

TEST(AnonymousProgramHierRef, PathReachingAModuleVariableIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "program q; int v = 3; endprogram\n"
      "program;\n"
      "  function int peek(); return top.x; endfunction\n"
      "endprogram\n"
      "program p;\n"
      "  initial $display(\"%0d\", peek());\n"
      "endprogram\n"
      "module top; int x = 4; q qi(); p pi(); endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 3, "24.3"));
}

TEST(AnonymousProgramHierRef, TaskCallIntoAnotherProgramIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program q; task automatic t; endtask initial #2; endprogram\n"
      "program;\n"
      "  task u; q.t(); endtask\n"
      "  task w; q.t; endtask\n"
      "endprogram\n"
      "module top; endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 3, "24.3"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 4, "24.3"));
}

}  // namespace
