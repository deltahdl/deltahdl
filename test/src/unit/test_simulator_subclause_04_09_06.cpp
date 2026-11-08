#include <gtest/gtest.h>

#include <string>
#include <utility>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PortConnectionSchedulingSim, InputPortDrivesLocalFromOutsideExpression) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u(8'hAB);\n"
      "endmodule\n",
      f, "u.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xABu);
}

TEST(PortConnectionSchedulingSim, InputPortFollowsOutsideChangesContinuously) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] src;\n"
      "  initial begin\n"
      "    src = 8'h11;\n"
      "    #5 src = 8'h22;\n"
      "  end\n"
      "  child u(src);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("u.a")->value.ToUint64(), 0x22u);
}

TEST(PortConnectionSchedulingSim, OutputPortDrivesOutsideFromLocalExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic [7:0] b);\n"
      "  assign b = 8'hCD;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] result;\n"
      "  child u(result);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("result")->value.ToUint64(), 0xCDu);
}

TEST(PortConnectionSchedulingSim, InoutPortSharesStorageWithOutsideNet) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module child(inout wire [7:0] data);\n"
      "  assign data = 8'hCD;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  child u(bus);\n"
      "endmodule\n",
      f, "bus");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(PortConnectionSchedulingSim, PrimitiveEvaluationProducesActiveUpdate) {
  SimFixture f;
  auto* out = RunAndFindVar(
      "module top;\n"
      "  logic in_sig;\n"
      "  wire out_sig;\n"
      "  initial in_sig = 1'b1;\n"
      "  buf b(out_sig, in_sig);\n"
      "endmodule\n",
      f, "out_sig");
  ASSERT_NE(out, nullptr);
  EXPECT_EQ(out->value.ToUint64() & 1u, 1u);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(PortConnectionSchedulingSim, PrimitiveOutputPreservesDriverStrength) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic in_sig;\n"
      "  wire out_sig;\n"
      "  initial in_sig = 1'b1;\n"
      "  buf b(out_sig, in_sig);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* net = f.ctx.FindNet("out_sig");
  ASSERT_NE(net, nullptr);
  ASSERT_FALSE(net->driver_strengths.empty());
  EXPECT_EQ(net->driver_strengths[0].s0, Strength::kStrong);
  EXPECT_EQ(net->driver_strengths[0].s1, Strength::kStrong);
}

TEST(PortConnectionSchedulingSim, NestedHierarchyPropagatesPortConnections) {
  SimFixture f;
  auto* x = RunAndFindVar(
      "module leaf(input logic [7:0] x);\n"
      "endmodule\n"
      "module mid(input logic [7:0] y);\n"
      "  leaf u_leaf(y);\n"
      "endmodule\n"
      "module top;\n"
      "  mid u_mid(8'h7E);\n"
      "endmodule\n",
      f, "u_mid.u_leaf.x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x7Eu);
}

TEST(PortConnectionSchedulingSim, PrimitiveInputAcceptsExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic a, b;\n"
      "  wire out_sig;\n"
      "  initial begin\n"
      "    a = 1'b1;\n"
      "    b = 1'b1;\n"
      "  end\n"
      "  buf bg(out_sig, a & b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("out_sig")->value.ToUint64() & 1u, 1u);
}

TEST(PortConnectionSchedulingSim,
     PrimitiveEvaluationSchedulesActiveUpdateOnInputChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic in_sig;\n"
      "  wire out_sig;\n"
      "  initial begin\n"
      "    in_sig = 1'b0;\n"
      "    #5 in_sig = 1'b1;\n"
      "  end\n"
      "  buf b(out_sig, in_sig);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("out_sig")->value.ToUint64() & 1u, 1u);
}

TEST(PortConnectionSchedulingSim, InputPortNetDrivenFromOutsideExpression) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module child(input wire [7:0] a);\n"
      "endmodule\n"
      "module top;\n"
      "  child u(8'h5C);\n"
      "endmodule\n",
      f, "u.a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x5Cu);
}

TEST(PortConnectionSchedulingSim, OutputPortDrivesOutsideNet) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module child(output logic [7:0] b);\n"
      "  assign b = 8'h3D;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] result;\n"
      "  child u(result);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 0x3Du);
}

TEST(PortConnectionSchedulingSim,
     PrimitiveInputAcceptsStructuralNetExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  logic [3:0] src;\n"
      "  wire [3:0] bus;\n"
      "  wire out_sig;\n"
      "  assign bus = src;\n"
      "  initial src = 4'b1000;\n"
      "  buf b(out_sig, bus[3]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("out_sig")->value.ToUint64() & 1u, 1u);
}

std::string RunAcrossInout(const std::string& child, const std::string& top) {
  SimFixture f;
  return RunCapture(child + "module top;\n" + top + "endmodule\n", f);
}

constexpr const char* kReadingChild =
    "module child(inout wire [3:0] p);\n"
    "  initial #1 $display(\"in=%b\", p);\n"
    "endmodule\n";

TEST(PortConnectionSchedulingSim, InoutPortCarriesAnOutsideValueInward) {
  std::string out = RunAcrossInout(kReadingChild,
                                   "  wire [3:0] bus;\n"
                                   "  assign bus = 4'b1001;\n"
                                   "  child u(.p(bus));\n");
  EXPECT_NE(out.find("in=1001"), std::string::npos) << out;
}

std::string RunInoutAgainst(const std::string& outside_drive) {
  return RunAcrossInout(
      "module child(inout wire p);\n"
      "  assign p = 1'b1;\n"
      "  initial #1 $display(\"in=%b\", p);\n"
      "endmodule\n",
      "  wire bus;\n" + outside_drive +
          "  child u(.p(bus));\n"
          "  initial #2 $display(\"out=%b\", bus);\n");
}

TEST(PortConnectionSchedulingSim, InoutPortSidesResolveAsOneNetwork) {
  std::string weaker = RunInoutAgainst("  assign (weak0, weak1) bus = 1'b0;\n");
  EXPECT_NE(weaker.find("in=1\nout=1"), std::string::npos) << weaker;
  std::string equal = RunInoutAgainst("  assign bus = 1'b0;\n");
  EXPECT_NE(equal.find("in=x\nout=x"), std::string::npos) << equal;
}

std::string StrengthAcrossInout(const std::string& strength, bool inward) {
  std::string drive =
      "  assign " + strength + (inward ? " bus" : " p") + " = 1'b1;\n";
  return RunAcrossInout("module child(inout wire p);\n" +
                            (inward ? std::string() : drive) +
                            "  initial #1 $display(\"in=%v\", p);\n"
                            "endmodule\n",
                        "  wire bus;\n" + (inward ? drive : std::string()) +
                            "  child u(.p(bus));\n"
                            "  initial #2 $display(\"out=%v\", bus);\n");
}

TEST(PortConnectionSchedulingSim, InoutPortPassesEveryStrengthUnreduced) {
  const std::pair<const char*, const char*> kDrives[] = {
      {"(weak0, weak1)", "We1"},
      {"(pull0, pull1)", "Pu1"},
      {"(strong0, strong1)", "St1"},
      {"(supply0, supply1)", "Su1"}};
  for (const auto& [strength, shown] : kDrives) {
    for (bool inward : {false, true}) {
      std::string out = StrengthAcrossInout(strength, inward);
      std::string both = std::string("in=") + shown + "\nout=" + shown;
      EXPECT_NE(out.find(both), std::string::npos)
          << strength << (inward ? " inward" : " outward") << ": " << out;
    }
  }
}

TEST(PortConnectionSchedulingSim, InoutPortOnASelectDrivesOnlyItsBitsOutward) {
  const char* const kChild =
      "module child(inout wire [1:0] p);\n"
      "  assign p = 2'b10;\n"
      "endmodule\n";
  const char* const kConnections[] = {"bus[2:1]", "bus[1 +: 2]", "bus[2 -: 2]"};
  for (const char* connection : kConnections) {
    std::string out =
        RunAcrossInout(kChild, std::string("  wire [3:0] bus;\n"
                                           "  assign bus[0] = 1'b1;\n"
                                           "  child u(.p(") +
                                   connection +
                                   "));\n"
                                   "  initial #1 $display(\"out=%b\", bus);\n");
    EXPECT_NE(out.find("out=z101"), std::string::npos)
        << connection << ": " << out;
  }
}

TEST(PortConnectionSchedulingSim, InoutPortOnASelectReadsItsBitsInward) {
  const char* const kConnections[] = {"bus[2:1]", "bus[1 +: 2]", "bus[2 -: 2]"};
  for (const char* connection : kConnections) {
    std::string out = RunAcrossInout(
        "module child(inout wire [1:0] p);\n"
        "  initial #1 $display(\"in=%b\", p);\n"
        "endmodule\n",
        std::string("  wire [3:0] bus;\n"
                    "  assign bus = 4'b0100;\n"
                    "  child u(.p(") +
            connection + "));\n");
    EXPECT_NE(out.find("in=10"), std::string::npos)
        << connection << ": " << out;
  }
}

TEST(PortConnectionSchedulingSim, InoutPortOnABitSelectJoinsThatBit) {
  std::string outward = RunAcrossInout(
      "module child(inout wire p);\n"
      "  assign p = 1'b0;\n"
      "endmodule\n",
      "  wire [1:0] bus;\n"
      "  assign bus[0] = 1'b1;\n"
      "  child u(.p(bus[1]));\n"
      "  initial #1 $display(\"out=%b\", bus);\n");
  EXPECT_NE(outward.find("out=01"), std::string::npos) << outward;
  std::string inward = RunAcrossInout(
      "module child(inout wire p);\n"
      "  initial #1 $display(\"in=%b\", p);\n"
      "endmodule\n",
      "  wire [1:0] bus;\n"
      "  assign bus = 2'b10;\n"
      "  child u(.p(bus[1]));\n");
  EXPECT_NE(inward.find("in=1"), std::string::npos) << inward;
}

TEST(PortConnectionSchedulingSim, InoutPortOnAConcatenationJoinsEachPart) {
  std::string outward = RunAcrossInout(
      "module child(inout wire [3:0] p);\n"
      "  assign p = 4'b1001;\n"
      "endmodule\n",
      "  wire [1:0] hi;\n"
      "  wire [2:0] lo;\n"
      "  child u(.p({hi, lo[1:0]}));\n"
      "  initial #1 $display(\"out=%b %b\", hi, lo);\n");
  EXPECT_NE(outward.find("out=10 z01"), std::string::npos) << outward;
  std::string inward = RunAcrossInout(kReadingChild,
                                      "  wire [1:0] hi;\n"
                                      "  wire [2:0] lo;\n"
                                      "  assign hi = 2'b10;\n"
                                      "  assign lo = 3'b101;\n"
                                      "  child u(.p({hi, lo[1:0]}));\n");
  EXPECT_NE(inward.find("in=1001"), std::string::npos) << inward;
}

TEST(PortConnectionSchedulingSim,
     InoutPortOnAConcatenationWithAVariableIsReported) {
  SimFixture f;
  RunCapture(
      "module child(inout wire [1:0] p);\n"
      "  assign p = 2'b10;\n"
      "endmodule\n"
      "module top;\n"
      "  wire w;\n"
      "  logic v;\n"
      "  child u(.p({w, v}));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variable 'v' cannot be connected to inout port "
                            "'p'",
                            7, "23.3.3.3"));
}

struct JoinedBitSource {
  const char* kind;
  const char* port;
  const char* child_items;
  const char* bus;
  const char* top_items;
  const char* shown;
};

std::string RunJoinedBit(const JoinedBitSource& source,
                         const std::string& connection) {
  return RunAcrossInout(std::string("primitive ubuf(output o, input i);\n"
                                    "  table\n"
                                    "    0 : 0;\n"
                                    "    1 : 1;\n"
                                    "  endtable\n"
                                    "endprimitive\n"
                                    "module child(inout ") +
                            source.port + " p);\n" + source.child_items +
                            "  initial #2 $display(\"in=%v\", p);\n"
                            "endmodule\n",
                        std::string("  ") + source.bus + "\n" +
                            source.top_items + "  child u(.p(" + connection +
                            "));\n"
                            "  initial #3 $display(\"out=%v\", bus[1]);\n");
}

TEST(PortConnectionSchedulingSim, InoutPortOnSelectsJoinsEveryKindOfSource) {
  const char* const kHold =
      "  logic en;\n"
      "  initial begin\n"
      "    en = 1'b1;\n"
      "    #1 en = 1'b0;\n"
      "  end\n";
  const std::string kChargeIn =
      std::string(kHold) + "  assign bus = en ? 1'b1 : 1'bz;\n";
  const std::string kChargeOut =
      std::string(kHold) + "  assign p = en ? 1'b1 : 1'bz;\n";
  const char* const kUdpIn =
      "  logic s;\n"
      "  initial s = 1'b1;\n"
      "  ubuf g(bus, s);\n";
  const char* const kUdpOut =
      "  logic s;\n"
      "  initial s = 1'b1;\n"
      "  ubuf g(p, s);\n";
  const char* const kTranIn =
      "  wire o;\n"
      "  assign o = 1'b1;\n"
      "  tran t(bus, o);\n";
  const char* const kTranOut =
      "  wire o;\n"
      "  assign o = 1'b1;\n"
      "  tran t(p, o);\n";
  const JoinedBitSource kSources[] = {
      {"udp in", "wire", "", "wire [1:1] bus;", kUdpIn, "St1"},
      {"udp out", "wire", kUdpOut, "wire [1:1] bus;", "", "St1"},
      {"tran in", "wire", "", "wire [1:1] bus;", kTranIn, "St1"},
      {"tran out", "wire", kTranOut, "wire [1:1] bus;", "", "St1"},
      {"tri1 in", "wire", "", "tri1 [1:1] bus;", "", "Pu1"},
      {"tri1 out", "tri1", "", "wire [1:1] bus;", "", "Pu1"},
      {"tri0 in", "wire", "", "tri0 [1:1] bus;", "", "Pu0"},
      {"tri0 out", "tri0", "", "wire [1:1] bus;", "", "Pu0"},
      {"supply1 in", "wire", "", "supply1 [1:1] bus;", "", "Su1"},
      {"supply1 out", "supply1", "", "wire [1:1] bus;", "", "Su1"},
      {"supply0 in", "wire", "", "supply0 [1:1] bus;", "", "Su0"},
      {"supply0 out", "supply0", "", "wire [1:1] bus;", "", "Su0"},
      {"trireg in", "wire", "", "trireg [1:1] bus;", kChargeIn.c_str(), "Me1"},
      {"trireg out", "trireg", kChargeOut.c_str(), "wire [1:1] bus;", "",
       "Me1"},
      {"preset x in", "wire", "", "wire [1:1] bus;",
       "  assign #5 bus = 1'b1;\n", "StX"},
      {"preset x out", "wire", "  assign #5 p = 1'b1;\n", "wire [1:1] bus;", "",
       "StX"}};
  for (const JoinedBitSource& source : kSources) {
    for (const char* connection : {"bus[1]", "{bus[1]}"}) {
      std::string out = RunJoinedBit(source, connection);
      std::string both =
          std::string("in=") + source.shown + "\nout=" + source.shown;
      EXPECT_NE(out.find(both), std::string::npos)
          << source.kind << " through " << connection << ": " << out;
    }
  }
}

}  // namespace
