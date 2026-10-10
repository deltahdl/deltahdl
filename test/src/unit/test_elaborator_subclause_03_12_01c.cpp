#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "helpers_separate_units.h"

using namespace delta;

namespace {

// Elaborates `srcs` together, each a compilation unit of its own.
RtlirDesign* ElaborateUnits(const std::vector<std::string>& srcs,
                            ElabFixture& f, std::string_view top = "") {
  Elaborator elab(f.arena, f.diag,
                  ParseUnitsApart(srcs, f.mgr, f.arena, f.diag));
  auto* design = elab.Elaborate(top);
  f.has_errors = f.diag.HasErrors();
  return design;
}

// §3.12.1 with §3.13: each unit has a compilation-unit scope of its own, so a
// typedef of one name in each is two types, and each module reads the one its
// own unit declared, whichever unit the module instantiating it stands in.
TEST(SeparateCompilationUnits, EachUnitsTypedefIsItsOwn) {
  ElabFixture f;
  auto* design = ElaborateUnits({"typedef logic [3:0] word_t;\n"
                                 "module top;\n"
                                 "  word_t a;\n"
                                 "  child c();\n"
                                 "endmodule\n",
                                 "typedef logic [7:0] word_t;\n"
                                 "module child;\n"
                                 "  word_t b;\n"
                                 "endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* a = FindVar(design, "top", "a");
  const auto* b = FindVar(design, "child", "b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->width, 4u);
  EXPECT_EQ(b->width, 8u);
}

// §3.13: two units' scopes are two name spaces, so a variable of one name in
// each is no redeclaration, and each unit's module reads its own.
TEST(SeparateCompilationUnits, OneNameInTwoUnitsIsNoRedeclaration) {
  ElabFixture f;
  auto* design = ElaborateUnits({"int g;\n"
                                 "module top;\n"
                                 "  int x;\n"
                                 "  initial x = g;\n"
                                 "  child c();\n"
                                 "endmodule\n",
                                 "int g;\n"
                                 "module child;\n"
                                 "  int y;\n"
                                 "  initial y = g;\n"
                                 "endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §3.12.1: a unit's declarations are accessible only within that unit, so a
// module of another unit reading the name finds nothing it declares.
TEST(SeparateCompilationUnits, AnotherUnitsVariableIsUnresolved) {
  ElabFixture f;
  ElaborateUnits({"int shared;\n"
                  "module a; endmodule\n",
                  "module top;\n"
                  "  int y;\n"
                  "  initial y = shared;\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'shared'", 3, "23.9"));
}

TEST(SeparateCompilationUnits, AnotherUnitsNameUnderDollarUnitIsUndeclared) {
  ElabFixture f;
  ElaborateUnits({"int g;\n"
                  "module a; endmodule\n",
                  "module top;\n"
                  "  int y;\n"
                  "  initial y = $unit::g;\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier '$unit::g'", 3, "3.12.1"));
}

// §3.12.1: modules are visible in every unit, so one unit's module binds an
// instance written in another, and §23.3.1's top-level modules are chosen
// from the modules of every unit.
TEST(SeparateCompilationUnits, ModulesOfEveryUnitBindAndRootTheDesign) {
  ElabFixture f;
  auto* design = ElaborateUnits({"module top;\n"
                                 "  child c();\n"
                                 "endmodule\n",
                                 "module child;\n"
                                 "  logic [2:0] z;\n"
                                 "endmodule\n"},
                                f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_NE(FindVar(design, "child", "z"), nullptr);
}

// §3.12.1: packages are visible in every unit, so one unit imports a package
// another unit declared.
TEST(SeparateCompilationUnits, PackageOfOneUnitImportedInAnother) {
  ElabFixture f;
  auto* design = ElaborateUnits({"package p;\n"
                                 "  typedef logic [5:0] t;\n"
                                 "endpackage\n",
                                 "module top;\n"
                                 "  import p::*;\n"
                                 "  t v;\n"
                                 "endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "top", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 6u);
}

// A module instantiated from a module of its own unit stays in that unit's
// scope, the scope already in force where the instance is elaborated.
TEST(SeparateCompilationUnits, ModuleOfTheSameUnitKeepsItsScope) {
  ElabFixture f;
  auto* design = ElaborateUnits({"typedef logic [4:0] w_t;\n"
                                 "module top;\n"
                                 "  mid m();\n"
                                 "endmodule\n"
                                 "module mid;\n"
                                 "  w_t x;\n"
                                 "endmodule\n",
                                 "typedef logic [1:0] w_t;\n"
                                 "module other; endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindVar(design, "mid", "x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->width, 5u);
}

// §3.12.1: a task or function at compilation-unit scope is one of its unit's
// declarations, so the names it reads are searched for in that unit alone, and
// §23.9 reports one only another unit declares.
TEST(SeparateCompilationUnits, UnitFunctionReadingAnotherUnitsVariable) {
  ElabFixture f;
  ElaborateUnits({"int only_a;\n"
                  "module a; endmodule\n",
                  "function int f();\n"
                  "  return only_a;\n"
                  "endfunction\n"
                  "module top; endmodule\n"},
                 f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'only_a'", 2, "23.9"));
}

// §3.14.2.3 (printed page 60) makes it an error for some design elements of
// the design to have a time unit and precision and others not. The second
// unit's module takes its unit's own timeunit and timeprecision (rule c), so it
// has both, while the first unit's module has neither.
TEST(SeparateCompilationUnits, EachElementTakesItsOwnUnitsTimeScale) {
  ElabFixture f;
  ElaborateUnits({"module a; endmodule\n",
                  "timeunit 1ns;\n"
                  "timeprecision 1ps;\n"
                  "module b; endmodule\n"},
                 f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "some design elements specify time unit and "
                            "precision while others do not",
                            1, "3.14.2.3"));
}

// §24.6: an anonymous program's items share the name space of the scope the
// program stands in, which is its own unit's compilation-unit scope, so a
// function of one name in another unit collides with nothing.
TEST(SeparateCompilationUnits, AnonymousProgramSharesOnlyItsOwnUnitsNames) {
  ElabFixture f;
  ElaborateUnits({"program;\n"
                  "  function int f(); return 0; endfunction\n"
                  "endprogram\n"
                  "module a; endmodule\n",
                  "function int f(); return 1; endfunction\n"
                  "module b; endmodule\n"},
                 f);
  for (const auto& d : f.diag.Diagnostics()) EXPECT_NE(d.subclause, "24.6");
}

}  // namespace
