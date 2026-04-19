#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

static void VerifyExternInvPrimitive(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "inv");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "in");
  EXPECT_TRUE(udp->table.empty());
}

static void VerifyUdpRowInputs(const UdpTableRow& row,
                               const std::string& expected) {
  ASSERT_EQ(row.inputs.size(), expected.size());
  for (size_t j = 0; j < expected.size(); ++j) {
    EXPECT_EQ(row.inputs[j], expected[j]);
  }
}

struct SeqUdpRow {
  std::string inputs;
  char state;
  char output;
};

static void VerifySeqUdpTable(const UdpDecl* udp, const SeqUdpRow expected[],
                              size_t count) {
  ASSERT_EQ(udp->table.size(), count);
  for (size_t i = 0; i < count; ++i) {
    VerifyUdpRowInputs(udp->table[i], expected[i].inputs);
    EXPECT_EQ(udp->table[i].current_state, expected[i].state);
    EXPECT_EQ(udp->table[i].output, expected[i].output);
  }
}

struct CombUdpRow {
  std::string inputs;
  char output;
};

static void VerifyCombUdpTable(const UdpDecl* udp, const CombUdpRow expected[],
                               size_t count) {
  ASSERT_EQ(udp->table.size(), count);
  for (size_t i = 0; i < count; ++i) {
    VerifyUdpRowInputs(udp->table[i], expected[i].inputs);
    EXPECT_EQ(udp->table[i].output, expected[i].output);
  }
}

static void VerifyUdpInputNames(const UdpDecl* udp,
                                const std::string expected[], size_t count) {
  ASSERT_EQ(udp->input_names.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(udp->input_names[i], expected[i]);
  }
}

TEST(UdpDeclGrammar, CombinationalMux) {
  auto r = Parse(
      "primitive mux(output out, input a, b, sel);\n"
      "  table\n"
      "    0 ? 0 : 0;\n"
      "    1 ? 0 : 1;\n"
      "    ? 0 1 : 0;\n"
      "    ? 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "mux");
  EXPECT_EQ(udp->output_name, "out");
  EXPECT_FALSE(udp->is_sequential);
  std::string expected_inputs[] = {"a", "b", "sel"};
  VerifyUdpInputNames(udp, expected_inputs, std::size(expected_inputs));
  CombUdpRow expected_rows[] = {
      {"0?0", '0'}, {"1?0", '1'}, {"?01", '0'}, {"?11", '1'}};
  VerifyCombUdpTable(udp, expected_rows, std::size(expected_rows));
  EXPECT_EQ(udp->table[0].current_state, 0);
}

TEST(UdpDeclGrammar, CombinationalOrGate) {
  auto r = Parse(
      "primitive udp_or (output out, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "udp_or");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->table.size(), 4u);
  EXPECT_EQ(udp->table[0].output, '0');
  EXPECT_EQ(udp->table[3].output, '1');
}

TEST(UdpDeclGrammar, SequentialDff) {
  auto r = Parse(
      "primitive dff(output reg q, input d, clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  SeqUdpRow expected[] = {{"0r", '?', '0'}, {"1r", '?', '1'}};
  VerifySeqUdpTable(udp, expected, std::size(expected));
}

TEST(UdpDeclGrammar, SequentialWithInitial) {
  auto r = Parse(
      "primitive srff(output reg q, input s, input r);\n"
      "  initial q = 1'b0;\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
}

TEST(UdpDeclGrammar, SequentialLatch) {
  auto r = Parse(
      "primitive udp_latch (output reg q, input d, en);\n"
      "  initial q = 0;\n"
      "  table\n"
      "    1 1 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "    ? 0 : ? : -;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  const auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "udp_latch");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '0');
  ASSERT_EQ(udp->table.size(), 3u);

  EXPECT_EQ(udp->table[0].current_state, '?');
  EXPECT_EQ(udp->table[0].output, '1');
  EXPECT_EQ(udp->table[2].output, '-');
}

TEST(UdpDeclGrammar, SequentialUdpInitial) {
  auto r = Parse(
      "primitive srff(output reg q, input s, r);\n"
      "  initial q = 1'b1;\n"
      "  table\n"
      "    1 0 : ? : 1;\n"
      "    0 1 : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->udps.size(), 1);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_TRUE(udp->has_initial);
  EXPECT_EQ(udp->initial_value, '1');
}

TEST(UdpDeclGrammar, WildcardPort) {
  auto r = Parse(
      "primitive inv(.*);\n"
      "  output out;\n"
      "  input in;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "inv");
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "in");
  ASSERT_EQ(udp->table.size(), 2u);
}

TEST(UdpDeclGrammar, WildcardPortSequential) {
  auto r = Parse(
      "primitive dff(.*);\n"
      "  output reg q;\n"
      "  input d;\n"
      "  input clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
}

TEST(UdpDeclGrammar, MultipleUdps) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "primitive buf2(output out, input in);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_EQ(r.cu->udps[1]->name, "buf2");
}

TEST(UdpDeclGrammar, ExternAnsi) {
  auto r = Parse("extern primitive inv(output out, input in);\n");
  VerifyExternInvPrimitive(r);
}

TEST(UdpDeclGrammar, ExternNonAnsi) {
  auto r = Parse("extern primitive inv(out, in);\n");
  VerifyExternInvPrimitive(r);
}

TEST(UdpDeclGrammar, ExternAnsiSequential) {
  auto r = Parse("extern primitive dff(output reg q, input d, input clk);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->name, "dff");
  EXPECT_TRUE(udp->is_sequential);
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
}

TEST(UdpDeclGrammar, ExternThenDefinition) {
  auto r = Parse(
      "extern primitive inv(output out, input in);\n"
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_TRUE(r.cu->udps[0]->table.empty());
  EXPECT_EQ(r.cu->udps[1]->name, "inv");
  EXPECT_EQ(r.cu->udps[1]->table.size(), 2u);
}

TEST(UdpDeclGrammar, EndLabel) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive : inv\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(UdpDeclGrammar, EndLabelSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive : dff\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "dff");
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
}

TEST(UdpDeclGrammar, CombinationalUdpEndLabel) {
  auto r = Parse(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive : inv\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(UdpDeclGrammar, EndLabelMismatchIsError) {
  EXPECT_FALSE(ParseOk(
      "primitive inv(output y, input a);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive : wrong_name\n"));
}

TEST(UdpDeclGrammar, AttributeOnAnsiUdp) {
  auto r = Parse(
      "(* synthesis = \"off\" *)\n"
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(UdpDeclGrammar, AttributeOnNonAnsiUdp) {
  auto r = Parse(
      "(* synthesis = \"off\" *)\n"
      "primitive inv(out, in);\n"
      "  output out;\n"
      "  input in;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(UdpDeclGrammar, AttributeOnWildcardUdp) {
  auto r = Parse(
      "(* custom_attr *)\n"
      "primitive inv(.*);\n"
      "  output out;\n"
      "  input in;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

TEST(UdpDeclGrammar, AttributeOnExternUdp) {
  auto r = Parse(
      "(* custom_attr *)\n"
      "extern primitive inv(output out, input in);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
}

}  // namespace
