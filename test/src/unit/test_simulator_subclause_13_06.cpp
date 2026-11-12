#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"

using namespace delta;

namespace {

int Combine(int a, int b) { return a * 10 + b; }

void Store(int a, int* o) { *o = a + 1; }

int Twice(int a, int* o) {
  *o = a * 2;
  return 0;
}

int ticks = 0;

void Tick() { ++ticks; }

int Ticks() { return ticks; }

int Tock() {
  ticks += 10;
  return 0;
}

const std::map<std::string, void*>& CFunctions() {
  static const std::map<std::string, void*> kFunctions = {
      {"combine", reinterpret_cast<void*>(&Combine)},
      {"store", reinterpret_cast<void*>(&Store)},
      {"twice", reinterpret_cast<void*>(&Twice)},
      {"tick", reinterpret_cast<void*>(&Tick)},
      {"ticks", reinterpret_cast<void*>(&Ticks)},
      {"tock", reinterpret_cast<void*>(&Tock)},
  };
  return kFunctions;
}

constexpr const char* kImports =
    "  import \"DPI-C\" function int combine(input int a, input int b);\n"
    "  import \"DPI-C\" function void store(input int a, output int o);\n"
    "  import \"DPI-C\" task twice(input int a, output int o);\n";

uint64_t ValueOf(SimFixture& f, const std::string& name) {
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr) << name;
  return var == nullptr ? 0 : var->value.ToUint64();
}

void ExpectValues(SimFixture& f, const std::vector<std::string>& names,
                  const std::vector<uint64_t>& values) {
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  for (size_t i = 0; i < names.size(); ++i) {
    EXPECT_EQ(ValueOf(f, names[i]), values[i]) << names[i];
  }
}

TEST(ImportedSubroutineCallSim, AnImportIsCalledInEveryFormANativeOneTakes) {
  SimFixture f;
  RunWithImportsBound(std::string("module m;\n") + kImports +
                          "  int r1, r2, r3, r4, r5, r6;\n"
                          "  initial begin\n"
                          "    r1 = combine(1, 2);\n"
                          "    r2 = combine(.b(4), .a(3));\n"
                          "    store(8, r3);\n"
                          "    twice(21, r4);\n"
                          "    void'(combine(5, 6));\n"
                          "    r5 = combine(combine(0, 1), 2) + 1;\n"
                          "    store(.o(r6), .a(40));\n"
                          "  end\n"
                          "endmodule\n",
                      f, CFunctions(), "subclause_13_06_forms");
  ExpectValues(f, {"m.r1", "m.r2", "m.r3", "m.r4", "m.r5", "m.r6"},
               {12, 34, 9, 42, 13, 41});
}

void RunNoArgumentImports(SimFixture& f, const std::string& tick_call,
                          const std::string& tock_call) {
  ticks = 0;
  RunWithImportsBound(
      "module m;\n"
      "  import \"DPI-C\" function void tick();\n"
      "  import \"DPI-C\" task tock();\n"
      "  import \"DPI-C\" function int ticks();\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    " +
          tick_call +
          "\n"
          "    r1 = ticks();\n"
          "    " +
          tock_call +
          "\n"
          "    r2 = ticks();\n"
          "  end\n"
          "endmodule\n",
      f, CFunctions(), "subclause_13_06_no_arguments");
}

TEST(ImportedSubroutineCallSim,
     AVoidOrTaskImportWithNoArgumentsIsCalledWithEmptyParentheses) {
  SimFixture f;
  RunNoArgumentImports(f, "tick();", "tock();");
  ExpectValues(f, {"m.r1", "m.r2"}, {1, 11});
}

TEST(ImportedSubroutineCallSim,
     DISABLED_AVoidOrTaskImportWithNoArgumentsIsCalledWithoutParentheses) {
  SimFixture f;
  RunNoArgumentImports(f, "tick;", "tock;");
  ExpectValues(f, {"m.r1", "m.r2"}, {1, 11});
}

TEST(ImportedSubroutineCallSim, AnImportIsCalledFromEveryKindOfCaller) {
  SimFixture f;
  RunWithImportsBound(std::string("module m;\n") + kImports +
                          "  int r1, r2, r3, r4;\n"
                          "  wire [31:0] w = combine(7, 8);\n"
                          "  function int f1(int x); return combine(x, 1);"
                          " endfunction\n"
                          "  task t1(output int y); twice(5, y); endtask\n"
                          "  class C;\n"
                          "    function int g(); int v; store(2, v); return v;"
                          " endfunction\n"
                          "  endclass\n"
                          "  C c = new;\n"
                          "  initial begin\n"
                          "    r1 = f1(9);\n"
                          "    t1(r2);\n"
                          "    r3 = c.g();\n"
                          "    #1 r4 = w;\n"
                          "  end\n"
                          "endmodule\n",
                      f, CFunctions(), "subclause_13_06_callers");
  ExpectValues(f, {"m.r1", "m.r2", "m.r3", "m.r4"}, {91, 10, 3, 78});
}

TEST(ImportedSubroutineCallSim,
     AnImportDeclaredInAPackageOrTheUnitIsCalledLikeANativeOne) {
  SimFixture f;
  RunWithImportsBound(
      "package p;\n"
      "  import \"DPI-C\" function int combine(input int a, input int b);\n"
      "endpackage\n"
      "import \"DPI-C\" task twice(input int a, output int o);\n"
      "module m;\n"
      "  int r1, r2, r3;\n"
      "  initial begin\n"
      "    r1 = p::combine(2, 3);\n"
      "    twice(4, r2);\n"
      "    begin\n"
      "      import p::*;\n"
      "      r3 = combine(.a(6), .b(5));\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, CFunctions(), "subclause_13_06_scopes");
  ExpectValues(f, {"m.r1", "m.r2", "m.r3"}, {23, 8, 65});
}

TEST(ImportedSubroutineCallSim, AnImportIsCalledInAnInterfaceAndAProgram) {
  SimFixture f;
  RunWithImportsBound(
      "interface i;\n"
      "  import \"DPI-C\" function int combine(input int a, input int b);\n"
      "  int r;\n"
      "  initial r = combine(4, 4);\n"
      "endinterface\n"
      "program q;\n"
      "  import \"DPI-C\" task twice(input int a, output int o);\n"
      "  int r;\n"
      "  initial twice(13, r);\n"
      "endprogram\n"
      "module m;\n"
      "  i u();\n"
      "  q p1();\n"
      "endmodule\n",
      f, CFunctions(), "subclause_13_06_units");
  ExpectValues(f, {"m.u.r", "m.p1.r"}, {44, 26});
}

}  // namespace
