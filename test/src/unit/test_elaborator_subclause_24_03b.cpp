#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kProgramSignalRef =
    "hierarchical reference to program signal from outside the program is not "
    "permitted";

// §24.3 bars a reference to a program signal from outside any program block
// wherever the reference stands, so a display task's argument is reached as an
// assignment's side is.
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

// So is the value a module function returns.
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

// A name that reaches the program instance through the design, `top.pi.v`
// from another module, is a reference from outside any program block as much
// as `pi.v` written beside the instance is.
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

// §24.3 makes a hierarchical reference from one program scope to another
// legal, so the same path written in a program is not reported.
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

// §24.3: an anonymous program shall not contain a hierarchical reference to
// another program scope, and `top.qi.v` reaches the program instance qi of
// module top though no component of it names a program declaration.
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

// A path that reaches a module's own variable steps through no program scope,
// so the anonymous program may hold it.
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

}  // namespace
