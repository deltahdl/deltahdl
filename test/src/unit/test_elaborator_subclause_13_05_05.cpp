#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SubroutineCallElaborationSyntax, TaskCallWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x;\n"
      "    x = 8'd1;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidFunctionWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x;\n"
      "    x = 8'd1;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, NonvoidFunctionWithoutParensError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int get_val; return 1; endfunction\n"
      "  initial get_val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot omit parentheses in call to nonvoid function 'get_val'", 3,
      "13.5.5"));
}

TEST(SubroutineCallElaborationSyntax,
     NonvoidFunctionAllDefaultsWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int get_val(int v = 1); return v; endfunction\n"
      "  initial get_val;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot omit parentheses in call to nonvoid function 'get_val'", 3,
      "13.5.5"));
}

TEST(SubroutineCallElaborationSyntax, TaskAllDefaultsWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x(int v = 42);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax,
     VoidFunctionAllDefaultsWithoutParensElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x(int v = 42);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, VoidClassMethodNoArgsWithoutParensOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function void touch; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new();\n"
      "  initial c.touch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, ClassMethodAllDefaultsWithoutParensOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function void take(int v = 1); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new();\n"
      "  initial c.take;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineCallElaborationSyntax, TaskWithRequiredArgWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  task set_x(int v);\n"
      "    x = v;\n"
      "  endtask\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to 'set_x': not "
                            "all formal arguments have defaults",
                            6, "13.5.5"));
}

TEST(SubroutineCallElaborationSyntax,
     VoidFunctionWithRequiredArgWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  function void set_x(int v);\n"
      "    x = v;\n"
      "  endfunction\n"
      "  initial set_x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to 'set_x': not "
                            "all formal arguments have defaults",
                            6, "13.5.5"));
}

TEST(SubroutineCallElaborationSyntax,
     TaskWithMixedDefaultAndRequiredArgsWithoutParensIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  task compute(int a = 1, int b);\n"
      "    x = a + b;\n"
      "  endtask\n"
      "  initial compute;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot omit parentheses in call to 'compute': not "
                            "all formal arguments have defaults",
                            6, "13.5.5"));
}

TEST(SubroutineCallElaborationSyntax,
     NonvoidClassMethodBareNameIsNotARecursiveCall) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  function int foo();\n"
      "    foo = 3;\n"
      "    foo;\n"
      "    return foo;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

constexpr std::string_view kNonvoidOmitted =
    "cannot omit parentheses in call to nonvoid function '";

// Whether the call of the nonvoid function `name` at `line` was reported for
// leaving its parentheses off.
bool ReportedOmitted(const ElabFixture& f, std::string_view name,
                     uint32_t line) {
  return ReportedError(f.diag.Diagnostics(),
                       std::string(kNonvoidOmitted) + std::string(name) + "'",
                       line, "13.5.5");
}

// §27.1: a generate block's items are the module's like any other, so a call
// in any block of a conditional, case or loop generate construct, of a
// function the module declares or one the block itself does, keeps its
// parentheses as a call at the module's top level does.
TEST(OptionalArgumentListElaboration, ACallInAGenerateBlockIsJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter P = 1;\n"
      "  function int f(); return 1; endfunction\n"
      "  if (P) begin : g\n"
      "    function int h(); return 2; endfunction\n"
      "    initial begin f; h; end\n"
      "  end else begin : e\n"
      "    initial f;\n"
      "  end\n"
      "  case (P)\n"
      "    1: begin : c initial f; end\n"
      "  endcase\n"
      "  for (genvar i = 0; i < 1; i++) begin : l\n"
      "    initial f;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [name, line] :
       {std::pair{"f", 6u}, std::pair{"h", 6u}, std::pair{"f", 8u},
        std::pair{"f", 11u}, std::pair{"f", 14u}}) {
    EXPECT_TRUE(ReportedOmitted(f, name, line)) << name << " at " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

// In a method a name alone calls a method of the class or of a class it
// extends first (§8.13), which may leave its parentheses off; any other name
// calls the module's subroutine, whose call keeps them. A class nested in
// another sees the module's subroutines too (§8.23).
TEST(OptionalArgumentListElaboration, ACallInAMethodOfAModulesClassIsJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  class C;\n"
      "    function int g(); return 2; endfunction\n"
      "    function void run(); f; g; endfunction\n"
      "    class N;\n"
      "      function void go(); f; endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedOmitted(f, "f", 5));
  EXPECT_TRUE(ReportedOmitted(f, "f", 7));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// A class extending its type parameter declares names no one knows before the
// class is specialized, any of which a name alone may call, so a method's call
// by a name alone is not judged: here the default's method `f` is what it
// calls.
TEST(OptionalArgumentListElaboration, ACallInAClassOfAnUnknownBaseIsLeft) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  class Base;\n"
      "    function int f(); return 0; endfunction\n"
      "  endclass\n"
      "  class W #(type B = Base) extends B;\n"
      "    function void run(); f; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedOmitted(f, "f", 7));
}

// A class a package or the compilation unit declares calls the package's or
// the unit's subroutines by a name alone, and such a call keeps its
// parentheses as one in a module does.
TEST(OptionalArgumentListElaboration, ACallInAMethodOfAUnitOrPackageClass) {
  ElabFixture f;
  ElaborateSrc(
      "function int u(); return 3; endfunction\n"
      "class UC;\n"
      "  function void run(); u; endfunction\n"
      "endclass\n"
      "package p;\n"
      "  function int f(); return 1; endfunction\n"
      "  class C;\n"
      "    function void run(); f; endfunction\n"
      "  endclass\n"
      "endpackage\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedOmitted(f, "u", 3));
  EXPECT_TRUE(ReportedOmitted(f, "f", 8));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
