#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_vcd_var_decl.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdLogicTypeMapping : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(
        src, {.scope = "t",
              .registration = VcdSignalRegistration::kContextFiltered});
  }
};

TEST_F(VcdLogicTypeMapping, LogicVariableMasqueradesAsReg) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] bus;\n"
      "  initial begin\n"
      "    bus = 8'h00;\n"
      "    $dumpvars;\n"
      "    #1 bus = 8'hff;\n"
      "  end\n"
      "endmodule\n");
  auto bus = VarDecl(content, "bus");
  ASSERT_EQ(bus.size(), 6u) << content;
  EXPECT_EQ(bus[1], "reg") << content;
  EXPECT_EQ(bus[2], "8") << content;
}

TEST_F(VcdLogicTypeMapping, BitVariableMasqueradesAsRegAtTheSameWidth) {
  auto content = RunVcd(
      "module t;\n"
      "  bit [7:0] bus;\n"
      "  initial begin\n"
      "    bus = 8'h00;\n"
      "    $dumpvars;\n"
      "    #1 bus = 8'hff;\n"
      "  end\n"
      "endmodule\n");
  auto bus = VarDecl(content, "bus");
  ASSERT_EQ(bus.size(), 6u) << content;
  EXPECT_EQ(bus[1], "reg") << content;
  EXPECT_EQ(bus[2], "8") << content;
}

TEST_F(VcdLogicTypeMapping, ANetKeepsTheWireVarType) {
  auto content = RunVcd(
      "module t;\n"
      "  wire w;\n"
      "  logic d;\n"
      "  assign w = d;\n"
      "  initial begin d = 1'b0; $dumpvars; #1 d = 1'b1; end\n"
      "endmodule\n");
  auto w = VarDecl(content, "w");
  ASSERT_EQ(w.size(), 6u) << content;
  EXPECT_EQ(w[1], "wire") << content;
  EXPECT_EQ(w[2], "1") << content;
  auto d = VarDecl(content, "d");
  ASSERT_EQ(d.size(), 6u) << content;
  EXPECT_EQ(d[1], "reg") << content;
}

TEST_F(VcdLogicTypeMapping, ParametersAreDeclaredWithTheParameterVarType) {
  auto content = RunVcd(
      "package p;\n"
      "  parameter int PP = 5;\n"
      "  int pv;\n"
      "endpackage\n"
      "module c #(parameter W = 3) ();\n"
      "  logic [W-1:0] x;\n"
      "endmodule\n"
      "module t;\n"
      "  localparam bit [7:0] L = 8'hA5;\n"
      "  parameter real RP = 1.5;\n"
      "  c #(.W(4)) u();\n"
      "  initial begin $dumpvars; #1 p::pv = 1; end\n"
      "endmodule\n");
  for (const char* name : {"L", "RP", "W", "PP"}) {
    auto decl = VarDecl(content, name);
    ASSERT_EQ(decl.size(), 6u) << name << "\n" << content;
    EXPECT_EQ(decl[1], "parameter") << name << "\n" << content;
  }
  EXPECT_EQ(VarDecl(content, "L")[2], "8") << content;
  EXPECT_EQ(VarDecl(content, "RP")[2], "64") << content;
}

TEST_F(VcdLogicTypeMapping, PackageVariablesTakeTheirDeclaredTypesVarType) {
  auto content = RunVcd(
      "typedef struct packed { bit [2:0] x; } ps_t;\n"
      "typedef enum bit [1:0] {C, D} eb_t;\n"
      "package p;\n"
      "  int pi;\n"
      "  logic [3:0] pl;\n"
      "  time pt;\n"
      "  eb_t pe;\n"
      "  ps_t pp;\n"
      "endpackage\n"
      "module t;\n"
      "  initial begin $dumpvars; #1 p::pi = 1; end\n"
      "endmodule\n");
  struct Expected {
    const char* name;
    const char* var_type;
    const char* size;
  };
  for (const Expected& e :
       {Expected{"pi", "integer", "32"}, Expected{"pl", "reg", "4"},
        Expected{"pt", "time", "64"}, Expected{"pe", "reg", "2"},
        Expected{"pp", "reg", "3"}}) {
    auto decl = VarDecl(content, e.name);
    ASSERT_EQ(decl.size(), 6u) << e.name << "\n" << content;
    EXPECT_EQ(decl[1], e.var_type) << e.name << "\n" << content;
    EXPECT_EQ(decl[2], e.size) << e.name << "\n" << content;
  }
}

TEST_F(VcdLogicTypeMapping, TypedefOfAKeywordTypeTakesTheKeywordsVarType) {
  auto content = RunVcd(
      "typedef int myint;\n"
      "typedef time tm_t;\n"
      "typedef logic lg_t;\n"
      "module t;\n"
      "  myint v;\n"
      "  tm_t tm;\n"
      "  lg_t l;\n"
      "  initial begin $dumpvars; #1 v = 1; end\n"
      "endmodule\n");
  struct Expected {
    const char* name;
    const char* var_type;
    const char* size;
  };
  for (const Expected& e :
       {Expected{"v", "integer", "32"}, Expected{"tm", "time", "64"},
        Expected{"l", "reg", "1"}}) {
    auto decl = VarDecl(content, e.name);
    ASSERT_EQ(decl.size(), 6u) << e.name << "\n" << content;
    EXPECT_EQ(decl[1], e.var_type) << e.name << "\n" << content;
    EXPECT_EQ(decl[2], e.size) << e.name << "\n" << content;
  }
}

Variable* MakeVar(Arena& arena, uint32_t width) {
  auto* v = arena.Create<Variable>();
  v->value = MakeLogic4VecVal(arena, width, 0);
  return v;
}

TEST_F(VcdLogicTypeMapping, LogicVariableMapsToRegAtWriterStage) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.RegisterSignal(VcdSignalSpec{"lv", 8, MakeVar(arena_, 8),
                                     NetType::kWire, -1, -1,
                                     VcdDataType::kLogic});
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  auto lv = VarDecl(content, "lv");
  ASSERT_EQ(lv.size(), 6u) << content;
  EXPECT_EQ(lv[1], "reg");
  EXPECT_EQ(lv[2], "8");
}

}  // namespace
}  // namespace delta
