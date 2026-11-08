#include <gtest/gtest.h>

#include <algorithm>
#include <string>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(UdpStateTable, MissingTableKeywordRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  0 : 1;\n"
      "  1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'table', got integer literal", 2,
                            "29.3.4"));
}

TEST(UdpStateTable, MissingEndtableKeywordRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endtable', got EOF", 5, "29.3.4"));
}

TEST(UdpStateTable, RowMissingSemicolonRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got integer literal", 4, "29.3.4"));
}

TEST(UdpStateTable, InputFieldOrderFollowsHeaderPortList) {
  auto r = Parse(
      "primitive gate(output y, input a, input b, input c);\n"
      "  table\n"
      "    0 1 0 : 0;\n"
      "    1 0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
  ASSERT_EQ(udp->table.size(), 2u);
  ASSERT_EQ(udp->table[0].inputs.size(), 3u);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].inputs[1], '1');
  EXPECT_EQ(udp->table[0].inputs[2], '0');
}

TEST(UdpStateTable, InputFieldOrderIgnoresPortDeclarationOrder) {
  auto r = Parse(
      "primitive gate(q, a, b, c);\n"
      "  output q;\n"
      "  input c;\n"
      "  input b;\n"
      "  input a;\n"
      "  table\n"
      "    0 1 0 : 0;\n"
      "    1 0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
}

TEST(UdpStateTable, CombinationalRowHasInputsAndOutputOnly) {
  auto r = Parse(
      "primitive and2(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs.size(), 2u);
  EXPECT_EQ(udp->table[0].current_state, 0);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].output, '1');
}

TEST(UdpStateTable, SequentialRowHasInputsCurrentStateAndOutput) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : 1 : 0;\n"
      "    1 r : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 2u);
  EXPECT_EQ(udp->table[0].inputs.size(), 2u);
  EXPECT_EQ(udp->table[0].current_state, '1');
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[1].current_state, '0');
  EXPECT_EQ(udp->table[1].output, '1');
}

TEST(UdpStateTable, AllXInputsWithZeroOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

TEST(UdpStateTable, AllXInputsWithOneOutputRejected) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    x : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

TEST(UdpStateTable, AllXInputsWithXOutputAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : x;\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, DuplicateInputsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive bad(output y, input a, input b);\n"
      "  table\n"
      "    0 1 : 0;\n"
      "    0 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows covering the same combination of "
                            "inputs shall not specify different outputs",
                            4, "29.3.4"));
}

TEST(UdpStateTable, SequentialDuplicateInputsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive bad(output reg q, input d, input en);\n"
      "  table\n"
      "    0 1 : ? : 0;\n"
      "    0 1 : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows covering the same combination of "
                            "inputs shall not specify different outputs",
                            4, "29.3.4"));
}

TEST(UdpStateTable, OverlappingRowsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive p (y, a, b);\n"
      "  output y;\n"
      "  input a, b;\n"
      "  table\n"
      "    1 1 : 1 ;\n"
      "    1 ? : 0 ;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows covering the same combination of "
                            "inputs shall not specify different outputs",
                            6, "29.3.4"));
}

TEST(UdpStateTable, OverlappingRowsWithTheSameOutputAccepted) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    1 1 : 1;\n"
      "    1 ? : 1;\n"
      "    0 b : 0;\n"
      "    0 ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, OverlappingEdgeRowsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    p 0 : 0 : 1;\n"
      "    (0x) ? : 0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows covering the same combination of "
                            "inputs shall not specify different outputs",
                            4, "29.3.4"));
}

TEST(UdpStateTable, NoChangeOutputConflictsWithAnotherStateRejected) {
  auto r = Parse(
      "primitive seq(output reg q, input d, input clk);\n"
      "  table\n"
      "    ? f : ? : -;\n"
      "    1 (10) : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows covering the same combination of "
                            "inputs shall not specify different outputs",
                            4, "29.3.4"));
}

TEST(UdpStateTable, NoChangeOutputMatchingTheStateAccepted) {
  auto r = Parse(
      "primitive seq(output reg q, input d, input clk);\n"
      "  table\n"
      "    ? f : ? : -;\n"
      "    1 (10) : 1 : 1;\n"
      "    ? * : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, LevelRowBesideEdgeRowWithAnotherOutputAccepted) {
  auto r = Parse(
      "primitive latch(output reg q, input d, input en);\n"
      "  table\n"
      "    1 1 : ? : 1;\n"
      "    (01) 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, JkEdgeFlipFlopMixingLevelAndEdgeRowsAccepted) {
  auto r = Parse(
      "primitive jk_edge_ff (q, clock, j, k, preset, clear);\n"
      "  output q; reg q;\n"
      "  input clock, j, k, preset, clear;\n"
      "  table\n"
      "    ? ?? 01 : ? : 1 ;\n"
      "    ? ?? *1 : 1 : 1 ;\n"
      "    ? ?? 10 : ? : 0 ;\n"
      "    ? ?? 1* : 0 : 0 ;\n"
      "    r 00 00 : 0 : 1 ;\n"
      "    r 00 11 : ? : - ;\n"
      "    r 01 11 : ? : 0 ;\n"
      "    r 10 11 : ? : 1 ;\n"
      "    r 11 11 : 0 : 1 ;\n"
      "    r 11 11 : 1 : 0 ;\n"
      "    f ?? ?? : ? : - ;\n"
      "    b *? ?? : ? : - ;\n"
      "    b ?* ?? : ? : - ;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, RowWithTwoInputTransitionsRejected) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) (10) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4"));
}

TEST(UdpStateTable, RowWithSingleInputTransitionAccepted) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b, input c);\n"
      "  table\n"
      "    (01) 0 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, IdenticalDuplicateRowsNotFlagged) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, RowWithTwoShorthandEdgesRejected) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    r f : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row shall contain at most one input transition", 3,
      "29.3.4"));
}

TEST(UdpStateTable, SequentialAllXInputsWithXOutputAccepted) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    x x : 0 : x;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, SequentialAllXInputsWithNonXOutputRejected) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    x x : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

TEST(UdpStateTable, DuplicateEdgeInputsWithDifferentOutputsRejected) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    (01) 0 : 0 : 0;\n"
      "    (01) 0 : 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "UDP table rows covering the same combination of "
                            "inputs shall not specify different outputs",
                            4, "29.3.4"));
}

TEST(UdpStateTable, DuplicateEdgeRowsWithSameOutputNotFlagged) {
  auto r = Parse(
      "primitive seq(output reg q, input a, input b);\n"
      "  table\n"
      "    (01) 0 : 0 : 0;\n"
      "    (01) 0 : 0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, AllXInputsWithOneOutputNames29_3_4) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    x x : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row with all-x inputs shall specify x output", 3,
      "29.3.4"));
}

TEST(UdpStateTable, MalformedRowNames29_3_4) {
  auto r = Parse(
      "primitive p(output y, input a);\n"
      "  table\n"
      "    0 : 1\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ';'", 4, "29.3.4"));
}

TEST(UdpStateTable, RowWithFewerFieldsThanInputsRejected) {
  auto r = Parse(
      "primitive p(output y, input a, input b, input c);\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row has 2 input field(s) but primitive 'p' declares",
      4, "29.3.4"));
}

TEST(UdpStateTable, SequentialRowWithMoreFieldsThanInputsRejected) {
  auto r = Parse(
      "primitive p(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r 0 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row has 3 input field(s) but primitive 'p' declares",
      3, "29.3.4"));
}

TEST(UdpStateTable, SequentialRowWidthCountsInputFieldsOnly) {
  auto r = Parse(
      "primitive p(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 (01) : ? : 0;\n"
      "    1 (01) : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(UdpStateTable, NonAnsiRowWidthIsReadOffTheInputDeclarations) {
  auto r = Parse(
      "primitive p(y, a, b);\n"
      "  output y;\n"
      "  input a, b;\n"
      "  table\n"
      "    0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row has 1 input field(s) but primitive 'p' declares",
      5, "29.3.4"));
}

TEST(UdpStateTable, RowWidthIsReportedOncePerTable) {
  auto r = Parse(
      "primitive p(output y, input a, input b);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "    0 0 0 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP table row has 1 input field(s) but primitive 'p' declares",
      3, "29.3.4"));
  auto width_reports =
      std::count_if(r.diags.begin(), r.diags.end(), [](const Diagnostic& d) {
        return d.message.find("UDP table row has") != std::string::npos;
      });
  EXPECT_EQ(width_reports, 1);
}

TEST(UdpStateTable, RowWidthIsNotReportedUnderAHeaderWithNoInputs) {
  auto r = Parse(
      "primitive p(output y);\n"
      "  table\n"
      "    0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags, "UDP shall have at least one input port",
                            1, "29.3.1"));
  auto width_reports =
      std::count_if(r.diags.begin(), r.diags.end(), [](const Diagnostic& d) {
        return d.message.find("UDP table row has") != std::string::npos;
      });
  EXPECT_EQ(width_reports, 0);
}

TEST(UdpStateTable, EdgeIndicatorInCombinationalRowRejected) {
  auto r = Parse(
      "primitive p (y, a, b);\n"
      "  output y;\n"
      "  input a, b;\n"
      "  table\n"
      "    (01) 1 : 1 ;\n"
      "    0 ? : 0 ;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "an edge indicator belongs to a sequential "
                            "entry",
                            5, "29.3.4"));
}

TEST(UdpStateTable, EdgeSymbolInCombinationalRowRejected) {
  auto r = Parse(
      "primitive p (y, a, b);\n"
      "  output y;\n"
      "  input a, b;\n"
      "  table\n"
      "    0 ? : 0 ;\n"
      "    1 r : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "an edge indicator belongs to a sequential "
                            "entry",
                            6, "29.3.4"));
}

}  // namespace
