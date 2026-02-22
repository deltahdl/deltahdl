// §non_lrm

#include <gtest/gtest.h>

#include <string>

#include "synthesis/aig.h"
#include "synthesis/netlist_writer.h"

using namespace delta;

namespace {

// =============================================================================
// EDIF output
// =============================================================================
TEST(NetlistWriter, EdifBasicStructure) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddAnd(a, b);
  g.AddOutput(c);

  std::string edif = NetlistWriter::WriteEdif(g, "top");

  EXPECT_NE(edif.find("edif"), std::string::npos);
  EXPECT_NE(edif.find("top"), std::string::npos);
  EXPECT_NE(edif.find("library"), std::string::npos);
  EXPECT_NE(edif.find("cell"), std::string::npos);
  EXPECT_NE(edif.find("interface"), std::string::npos);
}

// =============================================================================
// Multi-input, multi-output
// =============================================================================
TEST(NetlistWriter, BlifMultiInputMultiOutput) {
  AigGraph g;
  auto a = g.AddInput();
  auto b = g.AddInput();
  auto c = g.AddInput();
  auto ab = g.AddAnd(a, b);
  auto bc = g.AddAnd(b, c);
  auto out_or = g.AddOr(a, c);
  g.AddOutput(ab);
  g.AddOutput(bc);
  g.AddOutput(out_or);

  std::string blif = NetlistWriter::WriteBlif(g, "multi");

  EXPECT_NE(blif.find(".model multi"), std::string::npos);
  EXPECT_NE(blif.find(".end"), std::string::npos);
  // Three inputs and three outputs.
  const char *const kExpectedNames[] = {"i0", "i1", "i2", "o0", "o1", "o2"};
  for (const char *name : kExpectedNames) {
    EXPECT_NE(blif.find(name), std::string::npos);
  }
}

// =============================================================================
// Format dispatch
// =============================================================================
TEST(NetlistWriter, DispatchByFormat) {
  AigGraph g;
  auto a = g.AddInput();
  g.AddOutput(a);

  std::string blif = NetlistWriter::Write(g, "test", NetlistFormat::kBlif);
  std::string vlog = NetlistWriter::Write(g, "test", NetlistFormat::kVerilog);
  std::string json = NetlistWriter::Write(g, "test", NetlistFormat::kJson);
  std::string edif = NetlistWriter::Write(g, "test", NetlistFormat::kEdif);

  EXPECT_NE(blif.find(".model test"), std::string::npos);
  EXPECT_NE(vlog.find("module test"), std::string::npos);
  EXPECT_NE(json.find("\"test\""), std::string::npos);
  EXPECT_NE(edif.find("test"), std::string::npos);
}

}  // namespace
