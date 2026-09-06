#include <string>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor is
// well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_vcd_var_decl.h"
#include "simulator/coverage.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.5 Table 21-11's logic row, split out of
// test_simulator_subclause_21_07_05a.cpp when that file reached the line cap.
// The row reads `reg`, sized by the "Total size of packed dimension", which is
// the same cell the bit row above it carries -- and the a-file covers bit.
//
// The var_type is read as the whole $var line rather than searched for as a
// keyword, because `reg` and `wire` both appear elsewhere in a header, and the
// widths are more than one bit so that "total size of packed dimension" is
// asserted rather than coincided with by a scalar.
class VcdLogicTypeMapping : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(
        src, {.scope = "t",
              .registration = VcdSignalRegistration::kContextFiltered});
  }
};

// Table 21-11 gives logic the row `reg`, "Total size of packed dimension". The
// registration sent a logic variable down the §21.7.2.3 net default instead, so
// every dumped logic object was declared `wire` -- a var_type the table gives
// to no SystemVerilog data type. Driven from source, which is where the defect
// was: the writer's own mapping of VcdDataType::kLogic to reg was already
// right, and LogicVariableMapsToRegAtWriterStage below is what says so.
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

// The bit row of the same table, at the same width, so the two rows Table 21-11
// spells identically are asserted to produce identical declarations. The a-file
// covers bit through a packed-array collapse; this stands beside the logic case
// above at the width that case uses.
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

// §21.7.2.3 gives a net the wire var_type, and Table 21-11 is about data types
// rather than nets, so a net keeps `wire` while the variables above take `reg`.
// Without this the two cases above are satisfied by a registration that answers
// reg for every object it is handed.
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
  // And the variable driving it is the reg the table gives it, so the one dump
  // holds both var_types and neither answer is the whole file's.
  auto d = VarDecl(content, "d");
  ASSERT_EQ(d.size(), 6u) << content;
  EXPECT_EQ(d[1], "reg") << content;
}

Variable* MakeVar(Arena& arena, uint32_t width) {
  auto* v = arena.Create<Variable>();
  v->value = MakeLogic4VecVal(arena, width, 0);
  return v;
}

// Table 21-11: logic masquerades as reg, asserted at the writer stage where the
// data type is supplied directly rather than derived from a declaration. This
// is the half of the rule that was always right -- the registration above is
// what sent a logic variable to the net default -- so the two together say
// which stage a future regression is in.
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
