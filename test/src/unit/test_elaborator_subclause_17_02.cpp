#include "fixture_checker_elab.h"
#include "fixture_elaborator.h"

namespace {

TEST(CheckerElab, ElaborateCheckerWithPorts) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker chk_ports(input logic clk, input logic rst);\n"
      "endchecker\n",
      f, "chk_ports");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

TEST(CheckerDeclaration, EmptyCheckerElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("checker chk; endchecker\n", f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, ModuleDeclaredInsideCheckerIsIllegal) {
  // §17.2: modules shall not be declared inside a checker.
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  module inner; endmodule\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerDeclaration, NestedCheckerDeclaredInsideCheckerIsLegal) {
  // §17.2: a checker body may contain further checker declarations.
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  checker inner; endchecker\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerDeclaration, ModuleInstantiatedInsideCheckerIsIllegal) {
  // §17.2: modules, interfaces, and programs shall not be instantiated inside
  // a checker; only checker instances are permitted.
  ElabFixture f;
  ElaborateSrc(
      "module m; endmodule\n"
      "checker chk;\n"
      "  m u1();\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerDeclaration, InterfaceDeclaredInsideCheckerIsIllegal) {
  // §17.2: interfaces shall not be declared inside a checker.
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  interface inner; endinterface\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerDeclaration, ProgramDeclaredInsideCheckerIsIllegal) {
  // §17.2: programs shall not be declared inside a checker.
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  program inner; endprogram\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerDeclaration, InterfaceInstantiatedInsideCheckerIsIllegal) {
  // §17.2: interfaces shall not be instantiated inside a checker; only checker
  // instances are permitted.
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; endinterface\n"
      "checker chk;\n"
      "  ifc u1();\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

TEST(CheckerDeclaration, ProgramInstantiatedInsideCheckerIsIllegal) {
  // §17.2: programs shall not be instantiated inside a checker.
  ElabFixture f;
  ElaborateSrc(
      "program prog; endprogram\n"
      "checker chk;\n"
      "  prog u1();\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

// §17.2: an input checker formal argument shall not be modified by the checker.
// A checker input formal is net-typed, so the modification is rejected even
// though the variable-input rule (§23.3.3.2) would exempt a net.
TEST(CheckerDeclaration, InputFormalContinuousDriveIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  assign a = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(f.has_errors);
}

// §17.2 control: driving a checker's own local variable (not an input formal)
// from the same continuous assignment is legal, isolating the input-formal rule
// above from any general prohibition on continuous assignments in a checker.
TEST(CheckerDeclaration, LocalVariableContinuousDriveIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic a, input logic b);\n"
      "  logic c;\n"
      "  assign c = a & b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

// §17.2: the no-modification rule applies to input formals only; an output
// formal may be driven. This is the positive counterpart of the input-formal
// negative above, differing solely in the port direction.
TEST(CheckerDeclaration, OutputFormalContinuousDriveIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic b, output logic q);\n"
      "  assign q = b;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

// §17.2: only checkers may be instantiated inside a checker; instantiating a
// checker inside another checker is legal and elaborates cleanly. Positive
// counterpart of the module/interface/program instantiation prohibitions.
TEST(CheckerDeclaration, CheckerInstantiatedInsideCheckerIsLegal) {
  ElabFixture f;
  ElaborateSrc(
      "checker inner(input logic x); endchecker\n"
      "checker outer(input logic clk);\n"
      "  inner i1(clk);\n"
      "endchecker\n",
      f, "outer");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
