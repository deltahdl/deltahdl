#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_separate_units.h"
#include "simulator/dpi_binding.h"
#include "simulator/lowerer.h"
#include "simulator/unit_scopes.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Elaborates `srcs` together, each a compilation unit of its own (§3.12.1,
// printed page 56), and lowers the design. Null where elaboration failed.
RtlirDesign* LowerUnits(const std::vector<std::string>& srcs, SimFixture& f) {
  Elaborator elab(f.arena, f.diag,
                  ParseUnitsApart(srcs, f.mgr, f.arena, f.diag));
  auto* design = elab.Elaborate("");
  EXPECT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  if (design == nullptr) return nullptr;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  return design;
}

// The value the run left in the variable `name`, 0 where none stands under it.
uint64_t ValueOf(SimFixture& f, std::string_view name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

// Runs `srcs`, each a unit of its own, with `top` in the first and `child c()`
// in the second, and answers the values of the first's `a` and the second's
// `b`, each module setting its own from what its unit declares.
std::vector<uint64_t> RunTopAndChild(const std::vector<std::string>& srcs) {
  SimFixture f;
  if (LowerUnits(srcs, f) == nullptr) return {};
  f.scheduler.Run();
  return {ValueOf(f, "a"), ValueOf(f, "c.b")};
}

// §3.12.1 with §6.21: `int g;` in two units is two variables, so each unit's
// module reads its own, written bare or through `$unit::`.
TEST(SeparateUnitsSim, EachUnitsVariableIsItsOwn) {
  SimFixture f;
  ASSERT_NE(LowerUnits({"int g = 1;\n"
                        "module top;\n"
                        "  int a, sa;\n"
                        "  child c();\n"
                        "  initial begin a = g; sa = $unit::g; end\n"
                        "endmodule\n",
                        "int g = 2;\n"
                        "module child;\n"
                        "  int b, sb;\n"
                        "  initial begin b = g; sb = $unit::g; end\n"
                        "endmodule\n"},
                       f),
            nullptr);
  f.scheduler.Run();
  EXPECT_EQ(ValueOf(f, "a"), 1u);
  EXPECT_EQ(ValueOf(f, "sa"), 1u);
  EXPECT_EQ(ValueOf(f, "c.b"), 2u);
  EXPECT_EQ(ValueOf(f, "c.sb"), 2u);
}

// §3.12.1 with §13.4: each unit's function of one name is its own, called by
// the unit's modules and by the unit's own subroutines.
TEST(SeparateUnitsSim, EachUnitsFunctionIsItsOwn) {
  SimFixture f;
  ASSERT_NE(LowerUnits({"function int f(); return 10; endfunction\n"
                        "module top;\n"
                        "  int a;\n"
                        "  child c();\n"
                        "  initial a = f();\n"
                        "endmodule\n",
                        "function int f(); return 20; endfunction\n"
                        "function int via(); return f(); endfunction\n"
                        "module child;\n"
                        "  int b, bv;\n"
                        "  initial begin b = f(); bv = via(); end\n"
                        "endmodule\n"},
                       f),
            nullptr);
  f.scheduler.Run();
  EXPECT_EQ(ValueOf(f, "a"), 10u);
  EXPECT_EQ(ValueOf(f, "c.b"), 20u);
  EXPECT_EQ(ValueOf(f, "c.bv"), 20u);
}

// §3.12.1 with §8.3: each unit's class of one name is its own, so `new` in a
// module constructs its own unit's class.
TEST(SeparateUnitsSim, EachUnitsClassIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"class C; int v = 3; endclass\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial begin C h = new; a = h.v; end\n"
                            "endmodule\n",
                            "class C; int v = 4; endclass\n"
                            "class D; endclass\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial begin C h = new; b = h.v; end\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{3, 4}));
}

// §3.12.1 with §6.24.1: a cast to a unit's typedef sizes the value to that
// unit's type, 4 bits in the first unit and 6 in the second; a package's
// typedef is the same in both.
TEST(SeparateUnitsSim, EachUnitsTypedefIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"package q; typedef int qt; endpackage\n"
                            "typedef logic [3:0] t;\n"
                            "module top;\n"
                            "  int a;\n"
                            "  int x = 255;\n"
                            "  child c();\n"
                            "  initial a = t'(x);\n"
                            "endmodule\n",
                            "typedef logic [5:0] t;\n"
                            "module child;\n"
                            "  int b;\n"
                            "  int x = 255;\n"
                            "  initial b = t'(x);\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{15, 63}));
}

// §3.12.1 with §19.3: each unit's covergroup of one name is its own, so an
// instance a procedure constructs has its own unit's bins: one value sampled
// covers one of two bins in the first unit and one of four in the second.
TEST(SeparateUnitsSim, EachUnitsCovergroupIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"covergroup cg with function sample(int v);\n"
                            "  coverpoint v { bins b[] = {[0:1]}; }\n"
                            "endcovergroup\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial begin\n"
                            "    cg k = new;\n"
                            "    k.sample(0);\n"
                            "    a = int'(k.get_inst_coverage());\n"
                            "  end\n"
                            "endmodule\n",
                            "covergroup cg with function sample(int v);\n"
                            "  coverpoint v { bins b[] = {[0:3]}; }\n"
                            "endcovergroup\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial begin\n"
                            "    cg k = new;\n"
                            "    k.sample(0);\n"
                            "    b = int'(k.get_inst_coverage());\n"
                            "  end\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{50, 25}));
}

// §3.12.1 with §35.5.4: each unit's import of one SystemVerilog name is its
// own, so a call reaches the C function the module's own unit imported.
int SeparateUnitsAddOne(int x) { return x + 1; }
int SeparateUnitsAddTwo(int x) { return x + 2; }

TEST(SeparateUnitsSim, EachUnitsDpiImportIsItsOwn) {
  SimFixture f;
  auto* design =
      LowerUnits({"import \"DPI-C\" add_one = function int f(input int x);\n"
                  "module top;\n"
                  "  int a;\n"
                  "  child c();\n"
                  "  initial a = f(10);\n"
                  "endmodule\n",
                  "import \"DPI-C\" add_two = function int f(input int x);\n"
                  "module child;\n"
                  "  int b;\n"
                  "  initial b = f(10);\n"
                  "endmodule\n"},
                 f);
  ASSERT_NE(design, nullptr);
  ASSERT_NE(f.ctx.GetDpiRuntime(), nullptr);
  BindDpiImports(
      *f.ctx.GetDpiRuntime(),
      LookupIn({{"add_one", reinterpret_cast<void*>(&SeparateUnitsAddOne)},
                {"add_two", reinterpret_cast<void*>(&SeparateUnitsAddTwo)}}),
      CallBuildDir("separate_units_dpi"), "cc", f.diag);
  f.scheduler.Run();
  EXPECT_EQ(ValueOf(f, "a"), 11u);
  EXPECT_EQ(ValueOf(f, "c.b"), 12u);
}

// §3.12.1 with §26.3: a unit's import is a declaration of that unit's scope,
// so each unit's module reads the x its own unit imported.
TEST(SeparateUnitsSim, EachUnitsImportIsItsOwn) {
  EXPECT_EQ(RunTopAndChild({"package p1; int x = 5; endpackage\n"
                            "import p1::*;\n"
                            "module top;\n"
                            "  int a;\n"
                            "  child c();\n"
                            "  initial a = x;\n"
                            "endmodule\n",
                            "package p2; int x = 6; endpackage\n"
                            "import p2::*;\n"
                            "module child;\n"
                            "  int b;\n"
                            "  initial b = x;\n"
                            "endmodule\n"}),
            (std::vector<uint64_t>{5, 6}));
}

// §3.12.1: an instance's names reach the unit its module was declared in, and
// a name written in a generate block of the instance reaches the same unit,
// the block's prefix extending the instance's. A design of one unit records
// none.
TEST(SeparateUnitsSim, InstanceUnitIsTheNearestRecordedHolder) {
  UnitScopes units;
  units.SetInstanceUnit("", -1);
  EXPECT_FALSE(units.Separate());
  EXPECT_EQ(units.UnitOf("c."), -1);
  units.SetInstanceUnit("", 0);
  units.SetInstanceUnit("c.", 1);
  EXPECT_TRUE(units.Separate());
  EXPECT_EQ(units.UnitOf(""), 0);
  EXPECT_EQ(units.UnitOf("c.g."), 1);
  EXPECT_EQ(units.UnitOf("d."), 0);
  EXPECT_EQ(UnitScopes::ScopeName(-1), "$unit");
  EXPECT_EQ(UnitScopes::ScopeName(2), "$unit#2");
  EXPECT_TRUE(UnitScopes::IsUnitScope("$unit#2"));
  EXPECT_FALSE(UnitScopes::IsUnitScope("pkg"));
}

}  // namespace
