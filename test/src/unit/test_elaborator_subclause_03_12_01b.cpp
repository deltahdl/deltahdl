#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

// §3.12.1 (printed page 56) with §6.21 (printed 132): `int g;` outside every
// module is a variable of the compilation-unit scope, which is searched for a
// name the module's own scope does not declare, and §6.21 gives it a static
// lifetime a module's procedure may write into, so `initial g = 5;` and an
// always block's `g <= g + 1;` name nothing undeclared. Both were reported as
// "undeclared identifier 'g'" by ValidateScopeRules
// (elaborator_scope_rules.cpp), which admitted the module's own names and its
// imports' alone while the read side admitted the unit's; the unit's variables
// were written through a unit function until now.
TEST(CompilationUnitScopeWrites, UnitVariableWrittenByAModuleProcedure) {
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "module m;\n"
             "  logic clk;\n"
             "  initial g = 5;\n"
             "  always @(posedge clk) g <= g + 1;\n"
             "endmodule\n"));
}

// §23.9 (printed page 761): a task declared in the module is a scope nested in
// the module's, and a name its body writes that neither declares is searched
// for in the compilation-unit scope next (§3.12.1), so a module task's `g = 7`
// is as clean as a process's. A subroutine body never went through
// ValidateScopeRules, which is what let 7222ce9fe's test write the unit's
// variable through a unit function; this case holds the task's write clean
// whichever check it comes to go through.
TEST(CompilationUnitScopeWrites, UnitVariableWrittenByAModuleTask) {
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "module m;\n"
             "  task set_g; g = 7; endtask\n"
             "  initial set_g();\n"
             "endmodule\n"));
}

// §23.9 (printed page 761): a name declared in no scope the reference can
// reach is still reported at the assignment's line. The unit declares `g` and
// the module writes `h`, so a check that admitted every write once the unit
// declared anything would let this through.
TEST(CompilationUnitScopeWrites, WriteToANameDeclaredNowhereIsStillReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int g;\n"
             "module m;\n"
             "  initial h = 5;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'h'",
                            3, "23.9"));
}

// §3.12.1 (printed page 56): the module's own scope is searched before the
// compilation-unit scope, so a module declaring its own `int g` beside the
// unit's writes the module's, which the elaborated module holds as a variable
// of its own, and the write is clean. Whether the simulator's storage keeps
// the two apart is task #400's question, so this case reads the elaborator's
// side alone.
TEST(CompilationUnitScopeWrites, ModuleVariableShadowingTheUnitsIsTheModules) {
  ElabFixture f;
  auto* design = Elaborate(
      "int g = 1;\n"
      "module m;\n"
      "  int g;\n"
      "  initial g = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(FindVar(design, "m", "g"), nullptr);
}

}  // namespace
