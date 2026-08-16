#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "simulator/udp_eval.h"

using namespace delta;

namespace {

// Parses a four-input `gate(out, a, b, c, d)` UDP whose only variation is the
// `input` declaration style, then asserts the canonical a/b/c/d port list.
void ExpectGateFourInputs(const std::string& input_decls) {
  auto r = Parse(
      "primitive gate(out, a, b, c, d);\n"
      "  output out;\n" +
      input_decls +
      "  table\n"
      "    0 0 0 0 : 0;\n"
      "    1 1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 4u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "c");
  EXPECT_EQ(udp->input_names[3], "d");
}

TEST(UdpPortDeclaration, UdpCombinational) {
  auto r = Parse(
      "primitive mux2(output y, input a, input b, input s);\n"
      "  table\n"
      "    0 ? 0 : 0 ;\n"
      "    1 ? 0 : 1 ;\n"
      "    ? 0 1 : 0 ;\n"
      "    ? 1 1 : 1 ;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "mux2");
  EXPECT_FALSE(r.cu->udps[0]->is_sequential);
}

TEST(UdpPortDeclaration, SingleInput) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "out");
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "in");
  ASSERT_EQ(udp->table.size(), 2u);
  ASSERT_EQ(udp->table[0].inputs.size(), 1u);
  EXPECT_EQ(udp->table[0].inputs[0], '0');
  EXPECT_EQ(udp->table[0].output, '1');
}

TEST(UdpPortDeclaration, AnsiSequential) {
  auto r = Parse(
      "primitive dff(output reg q, input d, input clk);\n"
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
  ASSERT_EQ(udp->table.size(), 2u);
}

TEST(UdpPortDeclaration, NonAnsiSequentialWithReg) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
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
  EXPECT_EQ(udp->input_names[0], "d");
  EXPECT_EQ(udp->input_names[1], "clk");
}

TEST(UdpPortDeclaration, AnsiSharedInputKeyword) {
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
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 3u);
  EXPECT_EQ(udp->input_names[0], "a");
  EXPECT_EQ(udp->input_names[1], "b");
  EXPECT_EQ(udp->input_names[2], "sel");
}

TEST(UdpPortDeclaration, AnsiPortListMixedInputKeyword) {
  auto r = Parse(
      "primitive gate(output out, input a, input b, c);\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 1 : 1;\n"
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

TEST(UdpPortDeclaration, OutputDeclPlain) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  output out;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "out");
  EXPECT_FALSE(udp->is_sequential);
}

TEST(UdpPortDeclaration, AllThreeDeclarationAlternatives) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d;\n"
      "  input clk;\n"
      "  reg q;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "q");
  ASSERT_EQ(udp->input_names.size(), 2u);
  EXPECT_EQ(udp->input_names[0], "d");
  EXPECT_EQ(udp->input_names[1], "clk");
  EXPECT_TRUE(udp->is_sequential);
}

TEST(UdpPortDeclaration, InputDeclSingleId) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  output out;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "a");
}

TEST(UdpPortDeclaration, InputDeclMultipleIds) {
  ExpectGateFourInputs("  input a, b, c, d;\n");
}

TEST(UdpPortDeclaration, AttrOnOutputDecl) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  (* synthesis = \"off\" *) output out;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_EQ(udp->output_name, "out");
}

TEST(UdpPortDeclaration, AttrOnRegDecl) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d, clk;\n"
      "  (* synthesis = \"off\" *) reg q;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
}

TEST(UdpPortDeclaration, InputDeclMixedListAndSeparate) {
  ExpectGateFourInputs(
      "  input a, b;\n"
      "  input c;\n"
      "  input d;\n");
}

TEST(UdpPortDeclaration, InputDeclSeparateDecls) {
  auto r = Parse(
      "primitive gate(out, a, b, c);\n"
      "  output out;\n"
      "  input a;\n"
      "  input b;\n"
      "  input c;\n"
      "  table\n"
      "    0 0 0 : 0;\n"
      "    1 1 1 : 1;\n"
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

TEST(UdpPortDeclaration, AttrOnInputDecl) {
  auto r = Parse(
      "primitive inv(out, a);\n"
      "  output out;\n"
      "  (* synthesis = \"off\" *) input a;\n"
      "  table\n"
      "    0 : 1;\n"
      "    1 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  ASSERT_EQ(udp->input_names.size(), 1u);
  EXPECT_EQ(udp->input_names[0], "a");
}

TEST(UdpPortDeclaration, NineInputsSequential) {
  auto r = Parse(
      "primitive big_seq(output reg q, input i0, i1, i2, i3, i4, i5, i6, i7,"
      " clk);\n"
      "  table\n"
      "    0 0 0 0 0 0 0 0 r : ? : 0;\n"
      "    1 1 1 1 1 1 1 1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_TRUE(udp->is_sequential);
  ASSERT_EQ(udp->input_names.size(), 9u);
}

TEST(UdpPortDeclaration, TenInputsCombinational) {
  auto r = Parse(
      "primitive big_comb(output y, input a, b, c, d, e, f, g, h, i, j);\n"
      "  table\n"
      "    0 0 0 0 0 0 0 0 0 0 : 0;\n"
      "    1 1 1 1 1 1 1 1 1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* udp = r.cu->udps[0];
  EXPECT_FALSE(udp->is_sequential);
  ASSERT_EQ(udp->input_names.size(), 10u);
}

TEST(UdpPortDeclaration, OutputDeclMultipleNamesRejected) {
  auto r = Parse(
      "primitive bad(a, b, c);\n"
      "  output a, b;\n"
      "  input c;\n"
      "  table\n"
      "    0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  // The second name is where the output declaration stops being legal, so the
  // report is the `;` Parser::ParseUdpOutputDecl expects after the one name.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got ','", 2, "29.3.2"));
}

TEST(UdpPortDeclaration, RegDeclNotNamingOutputRejected) {
  auto r = Parse(
      "primitive bad(q, d, clk);\n"
      "  output q;\n"
      "  reg d;\n"
      "  input d;\n"
      "  input clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP reg declaration shall name the output port", 3, "29.3.2"));
}

// §29.3.2: "Sequential UDPs shall contain a reg declaration for the output
// port". The rows are A.5.3's `sequential_entry`, three fields separated by two
// colons, and the output declaration says nothing about a reg, so the two
// disagree. The report stands at the first row that says so.
TEST(UdpPortDeclaration, SequentialUdpWithoutRegRejected) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : ? : 0;\n"
      "    1 r : ? : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sequential UDP shall declare its output port reg",
                            5, "29.3.2"));
}

// §29.3.2: "Combinational UDPs cannot contain a reg declaration." The rows are
// A.5.3's `combinational_entry`, two fields separated by one colon, and the
// output is declared reg, so the two disagree. The EXPECT_FALSE is what holds
// the report to one per UDP: the second row breaks the rule exactly as the
// first does, and a report per row would stand there too.
TEST(UdpPortDeclaration, CombinationalUdpWithRegRejected) {
  auto r = Parse(
      "primitive c(output reg y, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "combinational UDP shall not declare its output port reg", 3,
      "29.3.2"));
  EXPECT_FALSE(ReportedError(
      r.diags, "combinational UDP shall not declare its output port reg", 4,
      "29.3.2"));
}

// §29.3.2: the same prohibition holds when the reg is written as a separate
// declaration alongside a plain output declaration (the non-ANSI first form)
// rather than inline as `output reg`.
TEST(UdpPortDeclaration, CombinationalUdpWithSeparateRegRejected) {
  auto r = Parse(
      "primitive c(y, a);\n"
      "  output y;\n"
      "  reg y;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "combinational UDP shall not declare its output port reg", 6,
      "29.3.2"));
}

// §29.3.2: the output port declaration is the keyword `output` followed by one
// output port name. The lower bound of "one name" is the rejecting counterpart
// of OutputDeclMultipleNamesRejected: an output declaration carrying no name is
// rejected.
TEST(UdpPortDeclaration, OutputDeclWithoutNameRejected) {
  auto r = Parse(
      "primitive p(out, a);\n"
      "  output ;\n"
      "  input a;\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "29.3.2"));
}

// §29.3.2: the input port declaration is the keyword `input` followed by one or
// more input port names. This is the negative of that rule -- an input
// declaration with no name violates the "one or more" lower bound and is
// rejected.
TEST(UdpPortDeclaration, InputDeclWithoutNameRejected) {
  auto r = Parse(
      "primitive p(out, a);\n"
      "  output out;\n"
      "  input ;\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 3, "29.3.2"));
}

// The same missing reg as SequentialUdpWithoutRegRejected, written so that
// nothing but the reg is wrong with the source. That case puts `?` in the
// current-state field, and Table 29-1 bars `?` from an output field, so a
// parser reading the row as combinational rejects it under §29.3.6 whether it
// enforces §29.3.2 or not. `0` is legal in both fields, which leaves the
// missing reg as the only thing to report.
TEST(UdpPortDeclaration,
     SequentialTableWithoutRegRejectedWhenTheStateFieldIsALegalOutputSymbol) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : 0 : 0;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sequential UDP shall declare its output port reg",
                            5, "29.3.2"));
}

// One missing reg is one mistake however many rows stand under it. Every row
// here disagrees with the output declaration, so a report per row would stand
// at lines 5, 6 and 7; the EXPECT_FALSE on line 6 is what fails then.
TEST(UdpPortDeclaration,
     SequentialTableWithoutRegReportsAtTheFirstOffendingRow) {
  auto r = Parse(
      "primitive dff(q, d, clk);\n"
      "  output q;\n"
      "  input d, clk;\n"
      "  table\n"
      "    0 r : 0 : 0;\n"
      "    1 r : 0 : 1;\n"
      "    1 r : 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sequential UDP shall declare its output port reg",
                            5, "29.3.2"));
  EXPECT_FALSE(ReportedError(r.diags,
                             "sequential UDP shall declare its output port reg",
                             6, "29.3.2"));
}

}  // namespace
