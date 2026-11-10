#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

struct IntegerType {
  std::string_view name;
  std::string_view bits_signed_unknown;
};

constexpr IntegerType kIntegerTypes[] = {
    {"shortint", "16 1 0"},
    {"int", "32 1 0"},
    {"longint", "64 1 0"},
    {"byte", "8 1 0"},
    {"bit", "1 0 0"},
    {"logic", "1 0 1"},
    {"reg", "1 0 1"},
    {"integer", "32 1 1"},
    {"time", "64 0 1"},
    {"shortint unsigned", "16 0 0"},
    {"int unsigned", "32 0 0"},
    {"longint unsigned", "64 0 0"},
    {"byte unsigned", "8 0 0"},
    {"integer unsigned", "32 0 1"},
    {"time signed", "64 1 1"},
    {"bit signed", "1 1 0"},
    {"logic signed", "1 1 1"},
    {"reg signed", "1 1 1"},
    {"int signed", "32 1 0"},
    {"bit [3:0]", "4 0 0"},
    {"logic [3:0]", "4 0 1"},
    {"reg [3:0]", "4 0 1"},
    {"bit signed [3:0]", "4 1 0"},
    {"logic signed [3:0]", "4 1 1"},
};

std::string Decls(std::string_view indent) {
  std::string out;
  for (std::size_t i = 0; i < std::size(kIntegerTypes); ++i) {
    out += std::string(indent) + std::string(kIntegerTypes[i].name) + " v" +
           std::to_string(i) + ";\n";
  }
  return out;
}

std::string Probe(std::string_view prefix) {
  std::string out;
  for (std::size_t i = 0; i < std::size(kIntegerTypes); ++i) {
    std::string v = std::string(prefix) + "v" + std::to_string(i);
    out += "    " + v + " = '1;\n";
    out += "    b = " + v + " < 0;\n";
    out += "    " + v + " = 'x;\n";
    out.append("    $display(\"%0d %0d %0d\", $bits(")
        .append(v)
        .append("), b, $isunknown(")
        .append(v)
        .append("));\n");
  }
  return out;
}

std::string Initial(std::string_view prefix) {
  return "  initial begin\n    bit b;\n" + Probe(prefix) + "  end\n";
}

std::string Expected() {
  std::string out;
  for (const auto& t : kIntegerTypes) {
    out += std::string(t.bits_signed_unknown) + "\n";
  }
  return out;
}

TEST(IntegerDataTypeTable, ModuleVariablesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n" + Decls("  ") + Initial("") + "endmodule\n", f),
      Expected());
}

TEST(IntegerDataTypeTable, GenerateBlockVariablesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  if (1) begin : g\n" + Decls("    ") +
                           Initial("") + "  end\nendmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, InterfaceVariablesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i;\n" + Decls("  ") + Initial("") +
                           "endinterface\nmodule t;\n  i ii();\nendmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, ProgramVariablesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n" + Decls("  ") + Initial("") +
                           "endprogram\nmodule t;\n  p pp();\nendmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, PackageVariablesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("package k;\n" + Decls("  ") + "endpackage\nmodule t;\n" +
                     Initial("k::") + "endmodule\n",
                 f),
      Expected());
}

TEST(IntegerDataTypeTable, CompilationUnitVariablesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(Decls("") + "module t;\n" + Initial("$unit::") + "endmodule\n",
                 f),
      Expected());
}

TEST(IntegerDataTypeTable, ClassPropertiesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n" + Decls("  ") +
                           "endclass\nmodule t;\n  C c = new;\n" +
                           Initial("c.") + "endmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, UnpackedStructMembersFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  typedef struct {\n" + Decls("    ") +
                           "  } S;\n  S s;\n" + Initial("s.") + "endmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, FunctionLocalsFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n  function automatic void fn();\n"
                       "    bit b;\n" +
                           Decls("    ") + Probe("") +
                           "  endfunction\n  initial fn();\nendmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, TaskLocalsFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n  task tk();\n    bit b;\n" + Decls("    ") +
                     Probe("") + "  endtask\n  initial tk();\nendmodule\n",
                 f),
      Expected());
}

std::string ReturningFunctions() {
  std::string out;
  for (std::size_t i = 0; i < std::size(kIntegerTypes); ++i) {
    std::string t(kIntegerTypes[i].name);
    std::string n = std::to_string(i);
    out.append("  function ").append(t).append(" o").append(n);
    out.append("(); return '1; endfunction\n");
    out.append("  function ").append(t).append(" x").append(n);
    out.append("(); return 'x; endfunction\n");
  }
  return out;
}

std::string ReturnProbe(std::string_view prefix) {
  std::string out = "  initial begin\n";
  for (std::size_t i = 0; i < std::size(kIntegerTypes); ++i) {
    std::string o = std::string(prefix) + "o" + std::to_string(i) + "()";
    std::string x = std::string(prefix) + "x" + std::to_string(i) + "()";
    out.append("    $display(\"%0d %0d %0d\", $bits(")
        .append(o)
        .append("), ")
        .append(o)
        .append(" < 0, $isunknown(")
        .append(x)
        .append("));\n");
  }
  return out + "  end\n";
}

TEST(IntegerDataTypeTable, ModuleFunctionReturnTypesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n" + ReturningFunctions() + ReturnProbe("") +
                           "endmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, PackageFunctionReturnTypesFollowTheTable) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package k;\n" + ReturningFunctions() +
                           "endpackage\nmodule t;\n" + ReturnProbe("k::") +
                           "endmodule\n",
                       f),
            Expected());
}

TEST(IntegerDataTypeTable, ByteHoldsAnAsciiCharacter) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  byte c = \"A\";\n"
                       "  byte unsigned d;\n"
                       "  initial begin\n"
                       "    d = \"z\";\n"
                       "    $display(\"%c%c %0d %0d\", c, d, c, d);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "Az 65 122\n");
}

}  // namespace
