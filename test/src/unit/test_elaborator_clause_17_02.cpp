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

}  // namespace
