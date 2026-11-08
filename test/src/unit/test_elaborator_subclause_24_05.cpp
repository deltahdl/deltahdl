#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ProgramSubroutineCall, ModuleCallingProgramTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task ptask; endtask\n"
      "  endprogram\n"
      "  initial p.ptask();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            5, "24.5"));
}

TEST(ProgramSubroutineCall, ModuleCallingProgramFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  program p;\n"
      "    function int pfunc; return 7; endfunction\n"
      "  endprogram\n"
      "  initial x = p.pfunc();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall, ModuleContAssignCallingProgramFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [7:0] w;\n"
      "  program p;\n"
      "    function logic [7:0] pfunc; return 8'd3; endfunction\n"
      "  endprogram\n"
      "  assign w = p.pfunc();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall, ProgramCallingOtherProgramTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  program p1;\n"
      "    task p1task(input int v); x = v; endtask\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial p1.p1task(9);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall, ProgramCallingDesignModuleTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  task dtask(input int v); x = v; endtask\n"
      "  program p;\n"
      "    initial dtask(5);\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall, ProgramTaskCallInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic ok;\n"
      "  program p;\n"
      "    task ptask; endtask\n"
      "  endprogram\n"
      "  initial assert (ok) p.ptask();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall, ProgramTaskCallInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic armed;\n"
      "  program pr;\n"
      "    task drain; endtask\n"
      "  endprogram\n"
      "  initial assert (armed) else pr.drain();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall, ProgramTaskCallInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program pk;\n"
      "    task pick; endtask\n"
      "  endprogram\n"
      "  initial randcase 1: pk.pick(); endcase\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            5, "24.5"));
}

TEST(ProgramSubroutineCall, ProgramTaskCallInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program ps;\n"
      "    task sample; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { ps.sample(); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            7, "24.5"));
}

TEST(ProgramSubroutineCall,
     ABlockLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    pkt p;\n"
      "    p.go();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall,
     ANestedBlockLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    begin\n"
      "      pkt p;\n"
      "      p.go();\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall,
     AProgramSubroutineCallWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  initial begin\n"
      "    p.go();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            9, "24.5"));
}

TEST(ProgramSubroutineCall, AProgramSubroutineCallInAModuleTaskBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  task work();\n"
      "    p.go();\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall,
     AProgramSubroutineCallInAModuleFunctionBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  function int work();\n"
      "    p.go();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall,
     ASubroutineLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  task work();\n"
      "    pkt p;\n"
      "    p.go();\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall,
     AFormalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  task work(pkt p);\n"
      "    p.go();\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall,
     AProgramSubroutineCallInAModuleClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class driver;\n"
      "    function void run();\n"
      "      p.go();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            7, "24.5"));
}

TEST(ProgramSubroutineCall,
     AMethodLocalOfAProgramInstanceNameIsNotAProgramSubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class driver;\n"
      "    function void run();\n"
      "      pkt p;\n"
      "      p.go();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall,
     AProgramSubroutineCallInANestedClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void run();\n"
      "        p.go();\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            8, "24.5"));
}

TEST(ProgramSubroutineCall,
     ANestedClassMethodLocalOfAProgramInstanceNameIsNotASubroutineCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  class pkt;\n"
      "    function void go(); endfunction\n"
      "  endclass\n"
      "  program p;\n"
      "    task go; endtask\n"
      "  endprogram\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void run();\n"
      "        pkt p;\n"
      "        p.go();\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramSubroutineCall, ModuleEnablingProgramTaskWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  task t; $display(\"t\"); endtask\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "  initial pi.t;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall, ModuleCallingTopLevelProgramTaskIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  task automatic t; $display(\"t\"); endtask\n"
      "  initial #2;\n"
      "endprogram\n"
      "module top;\n"
      "  initial #1 p.t();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
}

TEST(ProgramSubroutineCall, ModuleCallingTopLevelProgramFunctionIsOneError) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  function int f(); return 7; endfunction\n"
      "  initial #2;\n"
      "endprogram\n"
      "module top;\n"
      "  initial #1 $display(\"%0d\", p.f());\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "calling a program subroutine from within a design "
                            "module is not permitted",
                            6, "24.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
