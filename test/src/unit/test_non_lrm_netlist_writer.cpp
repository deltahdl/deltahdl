// §non-lrm:netlist_writer

#include <gtest/gtest.h>
#include <string>
#include "synthesis/aig.h"
#include "synthesis/netlist_writer.h"

using namespace delta;

namespace {

// =============================================================================
// BLIF output
// =============================================================================
TEST(NetlistWriter, BlifSimpleAnd) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  std::string blif = NetlistWriter::WriteBlif(g, "top");

  EXPECT_NE(blif.find(".model top"), std::string::npos);
  EXPECT_NE(blif.find(".inputs"), std::string::npos);
  EXPECT_NE(blif.find(".outputs"), std::string::npos);
  EXPECT_NE(blif.find(".end"), std::string::npos);
  // AND gate truth table row: both inputs high -> output high.
  EXPECT_NE(blif.find("11 1"), std::string::npos);
}

TEST(NetlistWriter, BlifConstantOutput) {
  AigGraph g;
  g.AddOutput(AigGraph::kConstFalse);
  g.AddOutput(AigGraph::kConstTrue);

  std::string blif = NetlistWriter::WriteBlif(g, "const_mod");

  EXPECT_NE(blif.find(".model const_mod"), std::string::npos);
  // Constant-0 output: empty cover (no rows) produces 0.
  // Constant-1 output: single row with no inputs produces 1.
  EXPECT_NE(blif.find(".outputs"), std::string::npos);
  EXPECT_NE(blif.find(".end"), std::string::npos);
}

// =============================================================================
// Verilog output
// =============================================================================
TEST(NetlistWriter, VerilogSimpleAnd) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  std::string vlog = NetlistWriter::WriteVerilog(g, "top");

  EXPECT_NE(vlog.find("module top"), std::string::npos);
  EXPECT_NE(vlog.find("input"), std::string::npos);
  EXPECT_NE(vlog.find("output"), std::string::npos);
  EXPECT_NE(vlog.find("endmodule"), std::string::npos);
  // Should contain an AND assign.
  EXPECT_NE(vlog.find('&'), std::string::npos);
}

TEST(NetlistWriter, VerilogConstantOutput) {
  AigGraph g;
  g.AddOutput(AigGraph::kConstFalse);
  g.AddOutput(AigGraph::kConstTrue);

  std::string vlog = NetlistWriter::WriteVerilog(g, "const_mod");

  EXPECT_NE(vlog.find("module const_mod"), std::string::npos);
  EXPECT_NE(vlog.find("1'b0"), std::string::npos);
  EXPECT_NE(vlog.find("1'b1"), std::string::npos);
  EXPECT_NE(vlog.find("endmodule"), std::string::npos);
}

// =============================================================================
// JSON output
// =============================================================================
TEST(NetlistWriter, JsonContainsExpectedKeys) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  std::string json = NetlistWriter::WriteJson(g, "top");

  EXPECT_NE(json.find("\"module\""), std::string::npos);
  EXPECT_NE(json.find("\"ports\""), std::string::npos);
  EXPECT_NE(json.find("\"cells\""), std::string::npos);
  EXPECT_NE(json.find("\"netnames\""), std::string::npos);
  EXPECT_NE(json.find("\"top\""), std::string::npos);
}

}  // namespace
