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

TEST(ProgramSignalReference, DISABLED_AnUpwardNameFromAChildModuleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program prg;\n"
      "  int v = 6;\n"
      "endprogram\n"
      "module c;\n"
      "  initial $display(\"%0d\", pp.v);\n"
      "endmodule\n"
      "module top;\n"
      "  prg pp();\n"
      "  c c1();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 5, "24.3"));
}

TEST(ProgramSignalReference, AnInterfaceInitialReadingIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "interface bus;\n"
      "  initial $display(\"%0d\", top.pi.v);\n"
      "endinterface\n"
      "module top;\n"
      "  p pi();\n"
      "  bus b();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 5, "24.3"));
}

TEST(ProgramSignalReference,
     DISABLED_ACompilationUnitFunctionReturningIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "function int peek();\n"
      "  return top.pi.v;\n"
      "endfunction\n"
      "module top;\n"
      "  p pi();\n"
      "  initial $display(\"%0d\", peek());\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 5, "24.3"));
}

TEST(ProgramSignalReference, APackageFunctionReturningIsRefusedAsAPackageItem) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "package pk;\n"
      "  function int peek();\n"
      "    return top.pi.v;\n"
      "  endfunction\n"
      "endpackage\n"
      "module top;\n"
      "  p pi();\n"
      "  initial $display(\"%0d\", pk::peek());\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "package item contains a hierarchical reference "
                            "'top'",
                            6, "26.2"));
}

TEST(ProgramSignalReference, AProgramPortReadFromTheModuleIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p(output int o);\n"
      "  initial o = 5;\n"
      "endprogram\n"
      "module top;\n"
      "  int w;\n"
      "  p pi(w);\n"
      "  initial #1 $display(\"%0d\", pi.o);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 7, "24.3"));
}

TEST(ProgramSignalReference, APathThroughRootIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  int v = 5;\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "  initial $display(\"%0d\", $root.top.pi.v);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kProgramSignalRef, 6, "24.3"));
}

TEST(ProgramExclusion, AUdpDeclaredAfterTheProgramIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  wire x, z;\n"
      "  inv u1(x, z);\n"
      "endprogram\n"
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; p pi(); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive cannot be instantiated inside program "
                            "'p'",
                            3, "24.3"));
}

TEST(ProgramExclusion, AnInterfaceDeclaredAfterTheProgramIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  bus inst();\n"
      "endprogram\n"
      "interface bus; endinterface\n"
      "module top; p pi(); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instantiations not allowed in programs", 2,
                            "24.3"));
}

TEST(ProgramExclusion, AProgramDeclaredAfterTheProgramIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  other inst();\n"
      "endprogram\n"
      "program other; endprogram\n"
      "module top; p pi(); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instantiations not allowed in programs", 2,
                            "24.3"));
}

}  // namespace
