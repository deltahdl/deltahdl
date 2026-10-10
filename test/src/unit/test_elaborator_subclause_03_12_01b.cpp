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

// §3.12.1 (printed page 56) with §6.10 (printed 108) and §10.3.2 (printed
// 249): an implicit net is assumed for a continuous assignment's target only
// where no scope the assignment can directly reference declares the name, and
// the compilation-unit scope is searched for a name the module's own scope
// does not declare, so `assign g = 1;` in a module drives the unit's `int g`,
// a variable §10.3.2 lets one continuous assignment drive.
// MaybeCreateImplicitNet (elaborator_items.cpp) asked the module's variables,
// nets, ports and parameters alone, so the module gained an implicit net `g`
// shadowing the unit's variable, and the assignment drove that net.
TEST(CompilationUnitScopeWrites, UnitVariableDrivenByAContinuousAssignment) {
  ElabFixture f;
  auto* design = Elaborate(
      "int g;\n"
      "module m;\n"
      "  assign g = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(FindNet(design, "m", "g"), nullptr);
}

// §6.10 (printed page 108): a continuous assignment's target declared in no
// scope the module can reach is still an implicit scalar net of the module,
// so with the unit declaring `g` and nothing declaring `h`, `assign h = 1;`
// gets the net as before. A check that admitted every target once the unit
// declared anything would make no net here.
TEST(CompilationUnitScopeWrites, NameDeclaredNowhereStillGetsAnImplicitNet) {
  ElabFixture f;
  auto* design = Elaborate(
      "int g;\n"
      "module m;\n"
      "  assign h = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_NE(FindNet(design, "m", "h"), nullptr);
}

// §3.12.1 (printed pages 56-57): a reference searches only the part of the
// compilation-unit scope written before it, and a name other than a task's or
// a function's has to be declared in the unit before it is referenced.
TEST(CompilationUnitScopeOrder, UnitTaskReadsUnitVariableDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "task t; int x; x = 5 + b; endtask\n"
      "bit b;\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unresolved identifier 'b'",
                            1, "23.9"));
}

TEST(CompilationUnitScopeOrder, ModuleWritesUnitVariableDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial g = 5;\n"
      "endmodule\n"
      "int g;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'g'",
                            2, "23.9"));
}

TEST(CompilationUnitScopeOrder, ModuleReadsUnitVariableDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = g;\n"
      "endmodule\n"
      "int g;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'g'", 3, "23.9"));
}

TEST(CompilationUnitScopeOrder, ModuleReadsUnitNetDeclaredAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  initial y = w;\n"
      "endmodule\n"
      "wire w;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'w'", 3, "23.9"));
}

// §6.10 (printed page 108): with the unit's `g` written after the module, the
// assignment's target is declared nowhere the module can reach, so it is the
// module's implicit net.
TEST(CompilationUnitScopeOrder,
     AssignTargetDeclaredLaterInUnitGetsImplicitNet) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  assign g = 1;\n"
      "endmodule\n"
      "int g;\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_NE(FindNet(design, "m", "g"), nullptr);
}

// §3.12.1: `$unit::b` selects a declaration of the unit and refers forward no
// more than `b` does, and a `$unit::` name the unit declares nowhere names
// nothing.
TEST(CompilationUnitScopeOrder, UnitScopedReferenceToLaterDeclaration) {
  ElabFixture f;
  ElaborateSrc(
      "task t; int x; x = 5 + $unit::b; endtask\n"
      "bit b;\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$unit::b' precedes its declaration", 1,
                            "3.12.1"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToNothing) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::nope;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier '$unit::nope'", 3,
                            "3.12.1"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferencesToEarlierDataAndAnyTaskOk) {
  EXPECT_TRUE(
      ElabOk("int a;\n"
             "module m;\n"
             "  int y;\n"
             "  initial begin y = $unit::a; $unit::later_task(); end\n"
             "endmodule\n"
             "task later_task; endtask\n"));
}

// §3.12.1: an import written at compilation-unit scope is part of the scope
// the references after it search, and no reference before it.
TEST(CompilationUnitScopeOrder, UnitImportAfterModuleDoesNotReachIt) {
  ElabFixture f;
  ElaborateSrc(
      "package p; int x = 1; endpackage\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endmodule\n"
      "import p::*;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'x'", 4, "23.9"));
}

TEST(CompilationUnitScopeOrder, UnitImportBeforeModuleReachesIt) {
  EXPECT_TRUE(
      ElabOk("package p; int x = 1; endpackage\n"
             "import p::*;\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "endmodule\n"));
}

// §3.12.1 with §23.9: a unit variable written after the module is out of the
// module's reach, but a name the module declares itself is the module's own,
// whatever kind of declaration gives it and whatever the unit writes later.
TEST(CompilationUnitScopeOrder, ModuleVariableShadowsALaterUnitVariable) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int x;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "endmodule\n"
             "int x;\n"));
}

TEST(CompilationUnitScopeOrder, ModuleParameterShadowsALaterUnitVariable) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  parameter int x = 1;\n"
             "  int y;\n"
             "  initial y = x;\n"
             "endmodule\n"
             "int x;\n"));
}

// §3.12.1: only a unit variable or net written later is out of reach; a later
// unit function of the name a module variable has leaves the read alone.
TEST(CompilationUnitScopeOrder, ModuleVariableNamedLikeALaterUnitFunction) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int f;\n"
             "  int y;\n"
             "  initial y = f;\n"
             "endmodule\n"
             "function int f(); return 1; endfunction\n"));
}

// §3.12.1 lets a unit task or function be named before it is written, and a
// function or a DPI import (§35.5.4) is one as much as a task is.
TEST(CompilationUnitScopeOrder, UnitScopedCallsToLaterFunctionAndImportOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int y;\n"
             "  initial begin\n"
             "    y = $unit::later_f(2);\n"
             "    y = $unit::c_add(1);\n"
             "  end\n"
             "endmodule\n"
             "function int later_f(int a); return a; endfunction\n"
             "import \"DPI-C\" function int c_add(int a);\n"));
}

// §3.12.1 with §6.19: an enumeration member declares a name of the scope its
// type stands in, so `$unit::GREEN` names the unit's member once it is
// written, and refers forward to it before.
TEST(CompilationUnitScopeOrder, UnitScopedReferenceToEarlierEnumMemberOk) {
  EXPECT_TRUE(
      ElabOk("typedef enum {RED, GREEN} color_t;\n"
             "module m;\n"
             "  int y;\n"
             "  initial y = $unit::GREEN;\n"
             "endmodule\n"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToLaterEnumMember) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::GREEN;\n"
      "endmodule\n"
      "typedef enum {RED, GREEN} color_t;\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$unit::GREEN' precedes its declaration", 3,
                            "3.12.1"));
}

// §3.12.1 with §8.23: `$unit::C::K` heads with the unit's class C, which is
// reached once it is written and refers forward to it before.
TEST(CompilationUnitScopeOrder, UnitScopedReferenceToEarlierClassNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; static int K = 3; endclass\n"
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::C::K;\n"
      "endmodule\n",
      f, "m");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "'$unit::C'", 4, "3.12.1"));
}

TEST(CompilationUnitScopeOrder, UnitScopedReferenceToLaterClass) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int y;\n"
      "  initial y = $unit::C::K;\n"
      "endmodule\n"
      "class C; static int K = 3; endclass\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'$unit::C' precedes its declaration", 3,
                            "3.12.1"));
}

}  // namespace
