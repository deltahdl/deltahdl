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
#include "parser/ast_specify.h"

using namespace delta;

namespace {

RtlirDesign* ElaborateUnits(const std::vector<std::string>& srcs,
                            ElabFixture& f, std::string_view top = "") {
  Elaborator elab(f.arena, f.diag,
                  ParseUnitsApart(srcs, f.mgr, f.arena, f.diag));
  auto* design = elab.Elaborate(top);
  f.has_errors = f.diag.HasErrors();
  return design;
}

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

TEST(SeparateCompilationUnits, PackageItemOfOneUnitReachedByScopeResolution) {
  ElabFixture f;
  auto* design = ElaborateUnits({"package p;\n"
                                 "  parameter int K = 3;\n"
                                 "endpackage\n",
                                 "module top;\n"
                                 "  localparam int R = p::K;\n"
                                 "  logic [R-1:0] v;\n"
                                 "endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* v = FindVar(design, "top", "v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->width, 3u);
}

TEST(SeparateCompilationUnits, PrimitiveOfOneUnitInstantiatedInAnother) {
  ElabFixture f;
  auto* design = ElaborateUnits({"primitive myudp(output q, input d, e);\n"
                                 "  table\n"
                                 "    0 0 : 0;\n"
                                 "    0 1 : 0;\n"
                                 "    1 0 : 0;\n"
                                 "    1 1 : 1;\n"
                                 "  endtable\n"
                                 "endprimitive\n",
                                 "module top;\n"
                                 "  wire q;\n"
                                 "  logic d, e;\n"
                                 "  myudp (q, d, e);\n"
                                 "endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  const auto* top = design->top_modules[0];
  ASSERT_EQ(top->udp_insts.size(), 1u);
  ASSERT_NE(top->udp_insts[0].decl, nullptr);
  EXPECT_EQ(top->udp_insts[0].decl->name, "myudp");
}

TEST(SeparateCompilationUnits, InterfaceOfOneUnitInstantiatedInAnother) {
  ElabFixture f;
  auto* design = ElaborateUnits({"interface ifc;\n"
                                 "  logic s;\n"
                                 "endinterface\n",
                                 "module top;\n"
                                 "  ifc i();\n"
                                 "endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].inst_name, "i");
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[0].resolved->name, "ifc");
  EXPECT_TRUE(top->children[0].resolved->is_interface);
}

TEST(SeparateCompilationUnits, ProgramOfOneUnitInstantiatedInAnother) {
  ElabFixture f;
  auto* design = ElaborateUnits({"program prg;\n"
                                 "  int n;\n"
                                 "endprogram\n",
                                 "module top;\n"
                                 "  prg p();\n"
                                 "endmodule\n"},
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].inst_name, "p");
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[0].resolved->name, "prg");
  EXPECT_TRUE(top->children[0].resolved->is_program);
}

TEST(SeparateCompilationUnits, CheckerOfAnotherUnitsScopeIsNotVisible) {
  ElabFixture f;
  ElaborateUnits({"checker chk(input logic x);\n"
                  "endchecker\n"
                  "module a; endmodule\n",
                  "module top;\n"
                  "  logic v;\n"
                  "  chk c(v);\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "unknown module 'chk'", 3, "23.3.2"));

  ElabFixture g;
  auto* design = ElaborateUnits({"module a; endmodule\n",
                                 "checker chk(input logic x);\n"
                                 "endchecker\n"
                                 "module top;\n"
                                 "  logic v;\n"
                                 "  chk c(v);\n"
                                 "endmodule\n"},
                                g, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(g.has_errors);
}

TEST(SeparateCompilationUnits, AnotherUnitsTypedefIsNotAType) {
  ElabFixture f;
  ElaborateUnits({"typedef logic [3:0] t;\n"
                  "module a; endmodule\n",
                  "module top;\n"
                  "  t v;\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 't' does not precede", 2,
                            "6.18"));
}

TEST(SeparateCompilationUnits, AnotherUnitsClassIsNotAType) {
  ElabFixture f;
  ElaborateUnits({"class C;\n"
                  "endclass\n"
                  "module a; endmodule\n",
                  "module top;\n"
                  "  C h;\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "declaration of type 'C' does not precede", 2,
                            "6.18"));
}

TEST(SeparateCompilationUnits, AnotherUnitsFunctionAndTaskAreUndeclared) {
  ElabFixture f;
  ElaborateUnits({"function void fn();\n"
                  "endfunction\n"
                  "task tk;\n"
                  "endtask\n"
                  "module a; endmodule\n",
                  "module top;\n"
                  "  initial fn();\n"
                  "  initial tk();\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'fn'",
                            2, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'tk'",
                            3, "23.9"));
}

TEST(SeparateCompilationUnits, AnotherUnitsParameterIsUnresolved) {
  ElabFixture f;
  ElaborateUnits({"localparam int W = 8;\n"
                  "module a; endmodule\n",
                  "module top;\n"
                  "  int y = W;\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'W'", 2,
                            "23.9"));
}

TEST(SeparateCompilationUnits, AUnitsNetDeclarationAssignmentIsReported) {
  ElabFixture f;
  ElaborateUnits({"module top;\n"
                  "  child c();\n"
                  "endmodule\n",
                  "wire w = 1'b1;\n"
                  "module child; endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a net declaration with an implicit continuous "
                            "assignment cannot stand in the compilation-unit "
                            "scope",
                            1, "3.12.1"));
}

TEST(SeparateCompilationUnits, ProceduralAssignmentToItsOwnUnitsNet) {
  ElabFixture f;
  ElaborateUnits({"module top;\n"
                  "  child c();\n"
                  "endmodule\n",
                  "wire w;\n"
                  "module child;\n"
                  "  initial w = 1'b1;\n"
                  "endmodule\n"},
                 f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net 'w' cannot be the target of a procedural", 3,
                            "10.4"));
}

}  // namespace
