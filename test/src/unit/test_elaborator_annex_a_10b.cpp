#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(BnfClarificationElaboration, VoidMemberInASoftUnionError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  union soft { void v; bit [7:0] a; } u;\n"
      "  union soft packed { void w; bit [7:0] b; } p;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2u, 3u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "void member is only allowed in tagged unions",
                              line, "7.2"));
  }
}

TEST(BnfClarificationElaboration, SoftUnionWithoutAVoidMemberOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  union soft { bit [3:0] v; bit [7:0] a; } u;\n"
             "  union soft packed { bit [3:0] w; bit [7:0] b; } p;\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration, FinalOnAPureConstraintError) {
  ElabFixture f;
  ElaborateSrc(
      "virtual class B;\n"
      "  rand int x;\n"
      "  pure constraint e;\n"
      "endclass\n"
      "virtual class C extends B;\n"
      "  pure constraint :final c;\n"
      "  pure constraint :initial :final d;\n"
      "  pure constraint :extends :final e;\n"
      "  pure static constraint :final s;\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  for (uint32_t line : {6u, 7u, 8u, 9u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(),
                      "':final' shall not be specified on a pure constraint",
                      line, "18.5.2"));
  }
}

TEST(BnfClarificationElaboration, PureConstraintWithoutFinalOk) {
  EXPECT_TRUE(
      ElabOk("virtual class B;\n"
             "  rand int x;\n"
             "  pure constraint e;\n"
             "endclass\n"
             "virtual class C extends B;\n"
             "  pure constraint :initial c;\n"
             "  pure constraint :extends e;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(BnfClarificationElaboration, FinalOnANonPureConstraintPrototypeOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint :final c;\n"
             "  constraint :final d;\n"
             "endclass\n"
             "constraint :final C::c { x > 0; }\n"
             "constraint :final C::d { x < 9; }\n"
             "module m; endmodule\n"));
}

constexpr const char* kFunctionOverride =
    "a function's dynamic_override_specifiers belong on a class method "
    "declaration, and an interface class takes none";
constexpr const char* kTaskOverride =
    "a task's dynamic_override_specifiers belong on a class method "
    "declaration, and an interface class takes none";

TEST(BnfClarificationElaboration, DynamicOverrideOnAUnitTaskError) {
  ElabFixture f;
  ElaborateSrc(
      "task :initial t(); endtask\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTaskOverride, 1, "13.3"));
}

TEST(BnfClarificationElaboration, DynamicOverrideInInterfaceAndProgramError) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  function :initial int f(); return 1; endfunction\n"
      "  task :final t(); endtask\n"
      "endinterface\n"
      "program p;\n"
      "  function :final int g(); return 1; endfunction\n"
      "  task :initial u(); endtask\n"
      "endprogram\n"
      "module m;\n"
      "  ifc i();\n"
      "  p q();\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags, kFunctionOverride, 2, "13.4"));
  EXPECT_TRUE(ReportedError(diags, kTaskOverride, 3, "13.3"));
  EXPECT_TRUE(ReportedError(diags, kFunctionOverride, 6, "13.4"));
  EXPECT_TRUE(ReportedError(diags, kTaskOverride, 7, "13.3"));
}

TEST(BnfClarificationElaboration, DynamicOverrideOnACheckerFunctionError) {
  ElabFixture f;
  ElaborateSrc(
      "checker ck;\n"
      "  function :initial bit h(); return 1; endfunction\n"
      "endchecker\n"
      "module m;\n"
      "  ck c();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kFunctionOverride, 2, "13.4"));
}

TEST(BnfClarificationElaboration, CheckerFunctionWithoutASpecifierOk) {
  EXPECT_TRUE(
      ElabOk("checker ck;\n"
             "  function bit h(); return 1; endfunction\n"
             "endchecker\n"
             "module m;\n"
             "  ck c();\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration,
     DynamicOverrideOnAnInterfaceClassPrototypeError) {
  ElabFixture f;
  ElaborateSrc(
      "interface class I;\n"
      "  pure virtual function :initial void f();\n"
      "  pure virtual function :extends void g();\n"
      "  pure virtual function :final void h();\n"
      "  pure virtual task :initial t();\n"
      "endclass\n"
      "interface class J;\n"
      "  pure virtual function void k();\n"
      "endclass\n"
      "interface class K extends J;\n"
      "  pure virtual function :extends void k();\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  for (uint32_t line : {2u, 3u, 4u, 5u, 11u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "dynamic_override_specifiers shall not be used in an interface class",
        line, "8.26.1"));
  }
}

TEST(BnfClarificationElaboration, InterfaceClassPrototypeWithoutASpecifierOk) {
  EXPECT_TRUE(
      ElabOk("interface class I;\n"
             "  pure virtual function void f();\n"
             "  pure virtual task t();\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(BnfClarificationElaboration, DynamicOverrideOnAMethodOfAnyClassOk) {
  EXPECT_TRUE(
      ElabOk("class E;\n"
             "  extern virtual function :initial void f();\n"
             "endclass\n"
             "function void E::f(); endfunction\n"
             "package pk;\n"
             "  class P;\n"
             "    virtual function :initial void f(); endfunction\n"
             "  endclass\n"
             "endpackage\n"
             "class O;\n"
             "  class N;\n"
             "    virtual task :final t(); endtask\n"
             "  endclass\n"
             "endclass\n"
             "module m;\n"
             "  class M;\n"
             "    virtual function :initial void f(); endfunction\n"
             "  endclass\n"
             "endmodule\n"));
}

TEST(BnfClarificationElaboration,
     GeneralAlwaysInEveryCheckerGenerateFormIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic clk);\n"
      "  logic a, b, c;\n"
      "  generate\n"
      "    always @(posedge clk) a <= 1'b1;\n"
      "  endgenerate\n"
      "  if (1) always @(posedge clk) b <= 1'b1;\n"
      "  for (genvar i = 0; i < 1; i++) always @(posedge clk) c <= 1'b1;\n"
      "endchecker\n",
      f, "chk");
  for (uint32_t line : {4u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a general 'always' procedure cannot be used "
                              "inside checker 'chk'",
                              line, "17.5"))
        << line;
  }
}

TEST(BnfClarificationElaboration,
     AlwaysCombAndLatchInCheckerGenerateAreAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk(input logic en);\n"
      "  logic a, b, c, d;\n"
      "  if (1) begin : g\n"
      "    always_comb a = en;\n"
      "    always_latch if (en) b = 1'b1;\n"
      "  end\n"
      "  generate\n"
      "    always_comb c = en;\n"
      "  endgenerate\n"
      "  for (genvar i = 0; i < 1; i++) always_latch if (en) d = 1'b1;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
