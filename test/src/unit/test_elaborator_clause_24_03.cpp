#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_program.h"

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
  EXPECT_TRUE(f.has_errors);
}

// §24.3: nets declared in a program are program signals, exactly as program
// variables are, so a hierarchical reference to a program net from outside the
// program is an error too. The sibling test above uses a program variable; this
// covers the net input form, read through a continuous assignment in the
// enclosing module.
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
  EXPECT_TRUE(f.has_errors);
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
  // §24.3: a portless nested program that is not explicitly instantiated is
  // implicitly instantiated exactly once, and the implicit instance reuses the
  // declaration name. Counting the matching children observes the "once" part
  // of the rule, not just that some instance exists.
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
