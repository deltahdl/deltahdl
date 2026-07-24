#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §29.3: a UDP definition shall not appear between the module/program/
// interface/package keyword pairs. Each of the four container positions is a
// distinct syntactic input form and is witnessed separately: the module case
// here, and the program/interface/package cases in the three tests near the end
// of this file (built from their real dependency syntax).
TEST(UdpTopLevelParsing, PrimitiveInsideModuleRejected) {
  auto r = Parse(
      "module m;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpTopLevelParsing, PrimitiveBetweenModulesAccepted) {
  auto r = Parse(
      "module a; endmodule\n"
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

TEST(UdpTopLevelParsing, PrimitiveDefinedAfterInstantiationSiteParses) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  my_udp u1(y, a);\n"
      "endmodule\n"
      "primitive my_udp(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

TEST(UdpTopLevelParsing, AtLeast256UdpsAccepted) {
  std::string src;
  src.reserve(256UL * 96);
  for (int i = 0; i < 300; ++i) {
    src += "primitive p";
    src += std::to_string(i);
    src +=
        "(output out, input in);\n  table 0 : 1; 1 : 0; "
        "endtable\nendprimitive\n";
  }
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 300u);
}

// §29.3 head owns the `udp_declaration` production of Syntax 29-1, whose
// alternatives go beyond the two "alternate forms" that §29.3.1 describes in
// prose. The remaining alternatives -- the two `extern` prototype forms, the
// wildcard `( .* )` header, and the optional `endprimitive : udp_identifier`
// end label -- appear only in §29.3's syntax box, so they are witnessed here
// against the head's own canonical parser test.

// udp_declaration ::= ... | extern udp_ansi_declaration
TEST(UdpTopLevelParsing, ExternAnsiPrototypeAccepted) {
  auto r = Parse("extern primitive inv(output out, input in);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "inv");
  EXPECT_EQ(r.cu->udps[0]->output_name, "out");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "in");
  // A prototype carries no state table.
  EXPECT_TRUE(r.cu->udps[0]->table.empty());
}

// udp_declaration ::= ... | extern udp_nonansi_declaration
TEST(UdpTopLevelParsing, ExternNonAnsiPrototypeAccepted) {
  auto r = Parse("extern primitive inv(out, in);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "out");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "in");
}

// Second admitted output-declaration form inside the `extern
// udp_ansi_declaration` alternative: `output reg`. This drives the reg branch
// of the extern header path, which marks the prototype sequential -- a
// different code path than the plain `output` form witnessed above.
TEST(UdpTopLevelParsing, ExternAnsiSequentialPrototypeAccepted) {
  auto r = Parse("extern primitive dff(output reg q, input clk, input d);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "q");
  EXPECT_TRUE(r.cu->udps[0]->is_sequential);
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 2u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "clk");
  EXPECT_EQ(r.cu->udps[0]->input_names[1], "d");
}

// udp_declaration ::= ... | { attribute_instance } primitive udp_identifier
//                     ( .* ) ; { udp_port_declaration } udp_body endprimitive
TEST(UdpTopLevelParsing, WildcardPortListHeaderAccepted) {
  auto r = Parse(
      "primitive inv(.*);\n"
      "  output out;\n"
      "  input in;\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->output_name, "out");
  ASSERT_EQ(r.cu->udps[0]->input_names.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->input_names[0], "in");
}

// The `[ : udp_identifier ]` tail of udp_declaration: a matching end label is
// accepted...
TEST(UdpTopLevelParsing, MatchingEndprimitiveLabelAccepted) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive : inv\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

// ...and its negative form: an end label naming a different identifier than the
// UDP is rejected.
TEST(UdpTopLevelParsing, MismatchedEndprimitiveLabelRejected) {
  auto r = Parse(
      "primitive inv(output out, input in);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive : wrong\n");
  EXPECT_TRUE(r.has_errors);
}

// §29.3 head: a UDP definition shall not appear between program/endprogram,
// interface/endinterface, or package/endpackage (the module case is covered by
// PrimitiveInsideModuleRejected). Each container position is built from the
// real dependency syntax (§24.3 program, §25.3 interface, §26.2 package) rather
// than assumed to share the module path.
TEST(UdpTopLevelParsing, PrimitiveInsideProgramRejected) {
  auto r = Parse(
      "program p;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endprogram\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpTopLevelParsing, PrimitiveInsideInterfaceRejected) {
  auto r = Parse(
      "interface intf;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(UdpTopLevelParsing, PrimitiveInsidePackageRejected) {
  auto r = Parse(
      "package pkg;\n"
      "  primitive inv(output out, input in);\n"
      "    table 0 : 1; 1 : 0; endtable\n"
      "  endprimitive\n"
      "endpackage\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
