#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_included_keyword_elab.h"
#include "helpers_keyword_version.h"
#include "helpers_reported_error.h"
#include "helpers_reserved_keyword_elab.h"
#include "helpers_rtlir_lookup.h"
#include "model_keyword_table_sweeps.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {
TEST(SystemVerilog2012KeywordElaboration, IncludedWordsAreReservedAtThisStage) {
  for (const auto& table :
       {kVerilog1995KeywordSweep, kVerilog2001AddedKeywordSweep,
        kVerilog2005AddedKeywordSweep, kSystemVerilog2005AddedKeywordSweep,
        kSystemVerilog2009AddedKeywordSweep}) {
    ExpectKeywordTableIsReserved("1800-2012", table);
  }

  ExpectConfigurationWordsNameVariablesUnderNoconfig();
}

TEST(SystemVerilog2012KeywordElaboration, AddedWordsCannotNameVariables) {
  ExpectKeywordTableIsReserved("1800-2012",
                               kSystemVerilog2012AddedKeywordSweep);
}

TEST(SystemVerilog2012KeywordElaboration, AddedInterconnectNetsReachTheDesign) {
  const std::string kSrc =
      "module m (interconnect [3:0] p, inout interconnect [7:0] q,\n"
      "          input interconnect [1:0] r, output interconnect s,\n"
      "          input wire a, output wire y);\n"
      "  interconnect       scalar_ic;\n"
      "  interconnect [7:0] bus_ic;\n"
      "  wire         [7:0] plain;\n"
      "  assign y = a;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "scalar_ic");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kInterconnect);
  EXPECT_EQ(n->width, 1u);
  n = FindNet(design, "m", "bus_ic");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->net_type, NetType::kInterconnect);
  EXPECT_EQ(n->width, 8u);
  n = FindNet(design, "m", "plain");
  ASSERT_NE(n, nullptr);
  EXPECT_NE(n->net_type, NetType::kInterconnect);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 6u);
  struct PortCase {
    size_t index;
    Direction direction;
    uint32_t width;
  };
  const PortCase kMarked[] = {{0, Direction::kInout, 4},
                              {1, Direction::kInout, 8},
                              {2, Direction::kInput, 2},
                              {3, Direction::kOutput, 1}};
  for (const auto& c : kMarked) {
    EXPECT_TRUE(m->ports[c.index].is_interconnect) << c.index;
    EXPECT_EQ(m->ports[c.index].direction, c.direction) << c.index;
    EXPECT_EQ(m->ports[c.index].width, c.width) << c.index;
  }
  EXPECT_FALSE(m->ports[4].is_interconnect);

  ElabFixture signed_ic;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m (interconnect signed [3:0] p);\nendmodule\n"),
      signed_ic, "m");
  EXPECT_TRUE(ReportedError(signed_ic.diag.Diagnostics(),
                            "interconnect port 'p' shall not be declared "
                            "signed",
                            LineInRegion(1), "23.2.2.3"));
  ElabFixture signed_wire;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m (input wire signed [3:0] p);\nendmodule\n"),
      signed_wire, "m");
  EXPECT_FALSE(signed_wire.has_errors);

  ElabFixture ic_assign;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  interconnect [3:0] q = 4'd1;\nendmodule\n"),
      ic_assign, "m");
  EXPECT_TRUE(ReportedError(
      ic_assign.diag.Diagnostics(),
      "an interconnect net cannot be given a value where it is declared",
      LineInRegion(2), "10.3.1"));
  ElabFixture wire_assign;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  wire [3:0] q = 4'd1;\nendmodule\n"),
      wire_assign, "m");
  EXPECT_FALSE(wire_assign.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(In("1800-2009", kSrc), included,
                                               "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected ')', got identifier", LineInRegion(1),
                            "23.2.2.1"));
}

TEST(SystemVerilog2012KeywordElaboration,
     AddedNettypeDeclarationsResolveNetWidths) {
  const std::string kSrc =
      "module m;\n"
      "  function automatic real resolve_sum(input real drivers[]);\n"
      "    return 0.0;\n"
      "  endfunction\n"
      "  nettype logic [7:0] byte_net;\n"
      "  nettype byte_net    alias_net;\n"
      "  nettype real        analog_net with resolve_sum;\n"
      "  byte_net  wide;\n"
      "  alias_net through;\n"
      "  analog_net resolved;\n"
      "  wire      plain;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* n = FindNet(design, "m", "wide");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u);
  n = FindNet(design, "m", "through");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 8u) << "the second name resolves through the first";
  n = FindNet(design, "m", "resolved");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 64u);
  n = FindNet(design, "m", "plain");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->width, 1u);

  ElabFixture bad_type;
  ElaborateWithPreprocessor(
      In("1800-2012", "module m;\n  nettype string text_net;\nendmodule\n"),
      bad_type, "m");
  EXPECT_TRUE(ReportedError(bad_type.diag.Diagnostics(),
                            "data type of user-defined nettype 'text_net' is "
                            "not a legal nettype data type",
                            LineInRegion(2), "6.6.7"));

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(In("1800-2009", kSrc), included,
                                               "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected ';', got 'logic'", LineInRegion(5),
                            "6.8"));
}

TEST(SystemVerilog2012KeywordElaboration,
     AddedImplementsClauseCarriesObligations) {
  const std::string kSrc =
      "interface class reader;\n"
      "  pure virtual function int read();\n"
      "endclass\n"
      "interface class writer;\n"
      "  pure virtual function void write(int v);\n"
      "endclass\n"
      "class port_t implements reader, writer;\n"
      "  int held;\n"
      "  virtual function int read(); return held; endfunction\n"
      "  virtual function void write(int v); held = v; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 0;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  ElabFixture missing_read;
  ElaborateWithPreprocessor(In("1800-2012",
                               "interface class reader;\n"
                               "  pure virtual function int read();\n"
                               "endclass\n"
                               "class port_t implements reader;\n"
                               "  int held;\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            missing_read, "m");
  EXPECT_TRUE(ReportedError(missing_read.diag.Diagnostics(),
                            "class 'port_t' does not implement pure virtual "
                            "method 'read' from interface 'reader'",
                            LineInRegion(4), "8.26"));

  ElabFixture no_clause;
  ElaborateWithPreprocessor(In("1800-2012",
                               "interface class reader;\n"
                               "  pure virtual function int read();\n"
                               "endclass\n"
                               "class port_t;\n"
                               "  int held;\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            no_clause, "m");
  EXPECT_FALSE(no_clause.has_errors);

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(In("1800-2009", kSrc), included,
                                               "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected ';', got identifier", LineInRegion(7),
                            "8.3"));
}

TEST(SystemVerilog2012KeywordElaboration, AddedSoftQualifierReachesTheDesign) {
  const std::string kUnion =
      "module m;\n"
      "  typedef union soft { logic [7:0] a; logic [7:0] b; } overlay_t;\n"
      "  overlay_t u;\n"
      "  logic [7:0] plain;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kUnion), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* u = FindVar(design, "m", "u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(u->width, 8u) << "the members share their storage";

  ElabFixture union_included;
  ElaborateWithPreprocessorAllowingParseErrors(In("1800-2009", kUnion),
                                               union_included, "m");
  EXPECT_TRUE(ReportedError(union_included.diag.Diagnostics(),
                            "union declarations may not have a tag before '{'",
                            LineInRegion(2), "7.2"));

  const std::string kCyclic =
      "class c;\n"
      "  randc bit [3:0] v;\n"
      "  constraint cc { soft v == 4'd3; }\n"
      "endclass\n"
      "module m;\n"
      "  int result;\n"
      "  initial result = 0;\n"
      "endmodule\n";
  ElabFixture cyclic;
  ElaborateWithPreprocessor(In("1800-2012", kCyclic), cyclic, "m");
  EXPECT_TRUE(ReportedError(cyclic.diag.Diagnostics(),
                            "a soft constraint may not be specified on randc "
                            "variable 'v'",
                            LineInRegion(3), "18.5.13.1"));

  ElabFixture plain_rand;
  ElaborateWithPreprocessor(In("1800-2012",
                               "class c;\n"
                               "  rand bit [3:0] v;\n"
                               "  constraint cc { soft v == 4'd3; }\n"
                               "endclass\n"
                               "module m;\n"
                               "  int result;\n"
                               "  initial result = 0;\n"
                               "endmodule\n"),
                            plain_rand, "m");
  EXPECT_FALSE(plain_rand.has_errors);

  ElabFixture constraint_included;
  ElaborateWithPreprocessorAllowingParseErrors(In("1800-2009", kCyclic),
                                               constraint_included, "m");
  EXPECT_FALSE(ReportedError(constraint_included.diag.Diagnostics(),
                             "a soft constraint may not be specified on randc",
                             LineInRegion(3), "18.5.13.1"));
  EXPECT_TRUE(ReportedError(constraint_included.diag.Diagnostics(),
                            "the constraint block's items do not parse from "
                            "here",
                            LineInRegion(3), "A.1.10"));
}

TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog1995WordsStillBuildDesign) {
  ExpectVerilog1995DeclarationsElaborate("1800-2012");
}

TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog2005WordStillBuildsDesign) {
  ExpectVerilog2005DeclarationsElaborate("1800-2012");
}

TEST(SystemVerilog2012KeywordElaboration,
     IncludedVerilog2001WordsStillBuildDesign) {
  ExpectVerilog2001DeclarationsElaborate("1800-2012");
}

TEST(SystemVerilog2012KeywordElaboration,
     IncludedSystemVerilog2005WordsStillBuildDesign) {
  ExpectSystemVerilog2005DeclarationsElaborate("1800-2012");
}

TEST(SystemVerilog2012KeywordElaboration,
     IncludedTypeWordsFillTheDeclarationFormsSweepsMiss) {
  const std::string kSrc =
      "module ch (a, y);\n"
      "  input  [7:0] a;\n"
      "  output [7:0] y;\n"
      "  logic  [7:0] y;\n"
      "  always_comb y = a + a;\n"
      "endmodule\n"
      "module m (input logic clk, input logic d, output logic q);\n"
      "  int  counted = 21;\n"
      "  logic [7:0] as_logic;\n"
      "  wire  [7:0] ch_out;\n"
      "  ch u_ch (as_logic, ch_out);\n"
      "  always_comb q = d & clk;\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  const auto* counted = FindVar(design, "m", "counted");
  ASSERT_NE(counted, nullptr);
  EXPECT_EQ(counted->width, 32u);
  EXPECT_NE(counted->init_expr, nullptr);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->ports.size(), 3u);
  EXPECT_EQ(m->ports[0].type_kind, DataTypeKind::kLogic);
  EXPECT_EQ(m->ports[2].direction, Direction::kOutput);

  const auto* ch = FindModule(design, "ch");
  ASSERT_NE(ch, nullptr);
  ASSERT_EQ(ch->ports.size(), 2u);
  EXPECT_EQ(ch->ports[1].name, "y");
  EXPECT_EQ(ch->ports[1].direction, Direction::kOutput);
  const auto* y = FindVar(design, "ch", "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->width, 8u);
}

TEST(SystemVerilog2012KeywordElaboration,
     IncludedSystemVerilog2009WordsStillBuildDesign) {
  const std::string kSrc =
      "checker handshake (logic clk, logic req);\n"
      "  assert property (@(posedge clk) req);\n"
      "endchecker\n"
      "let gain = 21;\n"
      "module m (input logic clk, input logic req);\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] r;\n"
      "  let sum(untyped x, int y) = x + y;\n"
      "  global clocking gcb @(posedge clk); endclocking\n"
      "  restrict property (@(posedge clk) req);\n"
      "  handshake u_chk (clk, req);\n"
      "  initial begin\n"
      "    sel = 2'b01;\n"
      "    unique0 case (sel) 2'b01: r = 8'd1; default: r = 8'd0; endcase\n"
      "  end\n"
      "endmodule\n";

  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(In("1800-2012", kSrc), f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);

  ExpectLetDeclarationsElaborated(design);

  const auto* m = FindModule(design, "m");
  ASSERT_NE(m, nullptr);

  bool instance_seen = false;
  for (const auto& child : m->children) {
    if (child.inst_name == "u_chk") {
      EXPECT_EQ(child.module_name, "handshake");
      instance_seen = true;
    }
  }
  EXPECT_TRUE(instance_seen);

  bool qualified_case_seen = false;
  for (const auto& proc : m->processes) {
    if (proc.kind != RtlirProcessKind::kInitial || proc.body == nullptr)
      continue;
    for (auto* s : proc.body->stmts) {
      if (s != nullptr && s->kind == StmtKind::kCase) {
        EXPECT_EQ(s->qualifier, CaseQualifier::kUnique0);
        qualified_case_seen = true;
      }
    }
  }
  EXPECT_TRUE(qualified_case_seen);

  ElabFixture two_global;
  ElaborateWithPreprocessor(
      In("1800-2012",
         "module m (input logic clk);\n"
         "  global clocking gcb  @(posedge clk); endclocking\n"
         "  global clocking gcb2 @(negedge clk); endclocking\n"
         "endmodule\n"),
      two_global, "m");
  EXPECT_TRUE(ReportedError(two_global.diag.Diagnostics(),
                            "only one global clocking block is allowed per "
                            "scope",
                            LineInRegion(3), "14.14"));

  ElabFixture included;
  ElaborateWithPreprocessorAllowingParseErrors(In("1800-2005", kSrc), included,
                                               "m");
  EXPECT_TRUE(ReportedError(included.diag.Diagnostics(),
                            "expected top-level declaration", LineInRegion(1),
                            "3.12.1"));
}

TEST(SystemVerilog2012KeywordElaboration,
     EveryConstantFormResolvesUnderThisVersion) {
  ExpectEveryConstantFormResolves("1800-2012", "int ", "byte");
}

TEST(SystemVerilog2012KeywordElaboration,
     WordsOutsideTheTablesNameObjectsButAreNotTypes) {
  ExpectWordsNameObjectsButAreNotTypes(
      "1800-2012", {"implement", "implements_", "interconnects", "nettypes",
                    "net_type", "softly", "soft_"});
}

}  // namespace
