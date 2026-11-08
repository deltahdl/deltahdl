#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/ast_type.h"
#include "parser/parser.h"

using namespace delta;

static RtlirDesign* ElaborateSource(const std::string& src,
                                    ProgramElabFixture& f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

namespace {

TEST(ProgramElab, ElaborateProgramWithPorts) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_ports(input logic clk, input logic rst);\n"
      "endprogram\n",
      f, "prog_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

TEST(ProgramElab, ElaborateProgramWithInitialBlock) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program prog_init;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n",
      f, "prog_init");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_FALSE(mod->processes.empty());
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
}

TEST(ProgramConstruct, ProgramWithDataAndInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  logic [7:0] count;\n"
      "  int status;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    status = 1;\n"
      "  end\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, ProgramWithSubroutinesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  task do_work;\n"
      "  endtask\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, ProgramWithClassElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  class my_trans;\n"
      "    int data;\n"
      "  endclass\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, EmptyProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("program p; endprogram\n", f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, NestedProgramInModuleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    initial $display(\"nested\");\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, TwoNestedProgramsShareOuterVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int shared;\n"
      "  program p1;\n"
      "    initial shared = 1;\n"
      "  endprogram\n"
      "  program p2;\n"
      "    initial shared = 2;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "t");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, TopLevelPortlessProgramImplicitlyInstantiated) {
  ProgramElabFixture f;
  auto* design = ElaborateSource("program p; endprogram\n", f, "p");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->name, "p");
}

TEST(ProgramConstruct, ReferencingProgramSignalFromOutsideIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int psig;\n"
      "  endprogram\n"
      "  initial begin\n"
      "    p.psig = 1;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

TEST(ProgramConstruct, ReferencingProgramNetFromOutsideIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  wire w;\n"
      "  program p;\n"
      "    wire pnet;\n"
      "  endprogram\n"
      "  assign w = p.pnet;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

TEST(ProgramConstruct, ImplicitlyInstantiatedNestedProgramReusesDeclName) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "module top;\n"
      "  program p;\n"
      "    initial $display(\"hi\");\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  const auto* top = design->top_modules[0];
  int instances = 0;
  for (const auto& child : top->children) {
    if (child.module_name == "p") {
      EXPECT_EQ(child.inst_name, child.module_name);
      ++instances;
    }
  }
  EXPECT_EQ(instances, 1);
}

TEST(ProgramConstruct, HierRefBetweenProgramsIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program src;\n"
      "    int sig;\n"
      "  endprogram\n"
      "  program dst;\n"
      "    initial src.sig = 1;\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, AnonymousProgramHierRefToProgramIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program prog;\n"
      "  int psig;\n"
      "endprogram\n"
      "program;\n"
      "  task t;\n"
      "    prog.psig = 1;\n"
      "  endtask\n"
      "endprogram\n",
      f, "prog");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

constexpr std::string_view kProgramSignalFromOutside =
    "hierarchical reference to program signal from outside the program is not "
    "permitted";

void ExpectPackageAnonymousProgramHierRefRejected(
    const std::string& subroutine) {
  ElabFixture f;
  ElaborateSrc(
      "program prog;\n"
      "  int psig;\n"
      "endprogram\n"
      "package pkg;\n"
      "  program;\n" +
          subroutine +
          "  endprogram\n"
          "endpackage\n",
      f, "prog");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kProgramSignalFromOutside, 7,
                            "24.3"));
}

TEST(ProgramConstruct, PackageAnonymousProgramTaskHierRefToProgramIsError) {
  ExpectPackageAnonymousProgramHierRefRejected(
      "    task t;\n"
      "      prog.psig = 1;\n"
      "    endtask\n");
}

TEST(ProgramConstruct, PackageAnonymousProgramFunctionHierRefToProgramIsError) {
  ExpectPackageAnonymousProgramHierRefRejected(
      "    function void f();\n"
      "      prog.psig = 1;\n"
      "    endfunction\n");
}

TEST(ProgramConstruct, PackageAnonymousProgramWithoutHierRefElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program prog;\n"
      "  int psig;\n"
      "endprogram\n"
      "package pkg;\n"
      "  program;\n"
      "    task t;\n"
      "      int held;\n"
      "      held = 1;\n"
      "    endtask\n"
      "  endprogram\n"
      "endpackage\n",
      f, "prog");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, ProgramSignalRefInAnAssertionPassStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int psig;\n"
      "  endprogram\n"
      "  int q;\n"
      "  logic ok;\n"
      "  initial assert (ok) q = p.psig;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

TEST(ProgramConstruct, ProgramSignalRefInAnAssertionFailStatementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program pr;\n"
      "    int level;\n"
      "  endprogram\n"
      "  int depth;\n"
      "  logic armed;\n"
      "  initial assert (armed) else depth = pr.level;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

TEST(ProgramConstruct, ProgramSignalRefInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program pk;\n"
      "    int chosen;\n"
      "  endprogram\n"
      "  int taken;\n"
      "  initial randcase 1: taken = pk.chosen; endcase\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            6, "24.3"));
}

TEST(ProgramConstruct, ProgramSignalRefInARandsequenceCodeBlockIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program ps;\n"
      "    int sampled;\n"
      "  endprogram\n"
      "  int kept;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { kept = ps.sampled; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            8, "24.3"));
}

TEST(ProgramConstruct, ProgramSignalRefFromAnAnonymousProgramClassIsError) {
  ElabFixture f;
  ElaborateSrc(
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  class C;\n"
      "    function void work();\n"
      "      ps.sampled = 1;\n"
      "    endfunction\n"
      "  endclass\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

TEST(ProgramConstruct,
     ABlockLocalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  initial begin\n"
      "    s_t p;\n"
      "    q = p.a;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, AProgramSignalRefWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  initial begin\n"
      "    q = p.a;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

TEST(ProgramConstruct,
     AnAnonymousProgramSubroutineLocalOfAProgramNameIsNotAHierRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class pkt;\n"
      "  int sampled;\n"
      "endclass\n"
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  function void work();\n"
      "    pkt ps;\n"
      "    int x;\n"
      "    x = ps.sampled;\n"
      "  endfunction\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct,
     AnAnonymousProgramSubroutineFormalOfAProgramNameIsNotAHierRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class pkt;\n"
      "  int sampled;\n"
      "endclass\n"
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  function void work(pkt ps);\n"
      "    int x;\n"
      "    x = ps.sampled;\n"
      "  endfunction\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct,
     AnAnonymousProgramHierRefWithNoShadowingDeclarationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program ps;\n"
      "  int sampled;\n"
      "endprogram\n"
      "program;\n"
      "  function void work();\n"
      "    int x;\n"
      "    x = ps.sampled;\n"
      "  endfunction\n"
      "endprogram\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

TEST(ProgramConstruct, AProgramSignalRefInAModuleTaskBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  task work();\n"
      "    q = p.a;\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

TEST(ProgramConstruct, AProgramSignalRefInAModuleFunctionBodyIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  function int work();\n"
      "    q = p.a;\n"
      "    return q;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            7, "24.3"));
}

TEST(ProgramConstruct,
     ASubroutineLocalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  task work();\n"
      "    s_t p;\n"
      "    q = p.a;\n"
      "  endtask\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, AFormalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  function int work(s_t p);\n"
      "    q = p.a;\n"
      "    return q;\n"
      "  endfunction\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, AProgramSignalRefInAModuleClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  class driver;\n"
      "    function void run();\n"
      "      q = p.a;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            8, "24.3"));
}

TEST(ProgramConstruct,
     AMethodLocalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  class driver;\n"
      "    function void run();\n"
      "      s_t p;\n"
      "      q = p.a;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, AProgramSignalRefInANestedClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  int q;\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void run();\n"
      "        q = p.a;\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical reference to program signal from "
                            "outside the program is not permitted",
                            9, "24.3"));
}

TEST(ProgramConstruct,
     ANestedClassMethodLocalOfAProgramInstanceNameIsNotAProgramSignalRef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    int a;\n"
      "  endprogram\n"
      "  typedef struct { int a; } s_t;\n"
      "  int q;\n"
      "  class outer;\n"
      "    class inner;\n"
      "      function void run();\n"
      "        s_t p;\n"
      "        q = p.a;\n"
      "      endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramConstruct, ModuleDeclaredAfterProgramInstantiatingItIsError) {
  ProgramElabFixture f;
  ElaborateSource(
      "program p;\n"
      "  sub u0();\n"
      "endprogram\n"
      "module sub; endmodule\n",
      f, "p");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "instantiations not allowed in programs", 2,
                            "24.3"));
}

TEST(ProgramConstruct, AnUninstantiatedProgramIsATopLevelProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  int b;\n"
      "  initial b = 2;\n"
      "endprogram\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "p");
  EXPECT_TRUE(design->top_modules[0]->is_program);
}

TEST(ProgramConstruct, AnUninstantiatedProgramBesideAModuleIsATopToo) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "module t;\n"
      "  int a;\n"
      "endmodule\n"
      "program p;\n"
      "  int b;\n"
      "endprogram\n",
      f, "");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "t");
  EXPECT_EQ(design->top_modules[1]->name, "p");
}

TEST(ProgramConstruct, AnInstantiatedProgramIsNoTopLevelProgram) {
  ProgramElabFixture f;
  auto* design = ElaborateSource(
      "program p;\n"
      "  int b;\n"
      "endprogram\n"
      "module t;\n"
      "  p u();\n"
      "endmodule\n",
      f, "");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "t");
}

TEST(ProgramConstruct, ExternProgramPrototypeIsNoDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern program p(input logic a);\n"
      "program p(.*);\n"
      "endprogram\n"
      "module t;\n"
      "  logic a;\n"
      "  p u(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* prog = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(prog, nullptr);
  ASSERT_EQ(prog->ports.size(), 1u);
  EXPECT_EQ(prog->ports[0].direction, Direction::kInput);
}

TEST(ProgramConstruct, ExternProgramPrototypeIsNoTopLevelProgram) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "extern program p;\n"
      "program p;\n"
      "  int b;\n"
      "endprogram\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_FALSE(design->top_modules[0]->variables.empty());
  EXPECT_EQ(design->top_modules[0]->variables[0].name, "b");
}

TEST(ProgramConstruct, ExternProgramPortCountMismatchIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "extern program p(input logic a, input logic b);\n"
      "program p(input logic a);\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "program 'p' port count (1) does not match extern declaration (2)", 2,
      "23.5"));
}

}  // namespace
