#include "fixture_parser.h"

using namespace delta;

namespace {

// Collect every UDP instance parsed inside the first module of a unit.
std::vector<ModuleItem*> FindUdpInstances(ParseResult& r) {
  std::vector<ModuleItem*> out;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kUdpInst) out.push_back(item);
  }
  return out;
}

const char* udp_def =
    "primitive my_udp(output y, input a, input b);\n"
    "  table\n"
    "    0 0 : 0;\n"
    "    1 1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";

// §29.8 BNF udp_instantiation lists drive_strength and delay2 as optional
// prefixes, followed by a udp_instance carrying its terminal list. This
// observes one declaration that supplies every optional component at once and
// checks each lands on the parsed instance: the strength pair, both rise/fall
// delays (delay2), the instance name, and the output/input terminal list.
TEST(UdpInstantiation, ParsesAllInstantiationComponents) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp (strong0, strong1) #(2, 3) u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  auto* u = insts[0];
  EXPECT_EQ(u->inst_module, "my_udp");
  EXPECT_EQ(u->drive_strength0, 4u);  // strong0
  EXPECT_EQ(u->drive_strength1, 4u);  // strong1
  ASSERT_NE(u->gate_delay, nullptr);
  EXPECT_EQ(u->gate_delay->int_val, 2u);
  ASSERT_NE(u->gate_delay_fall, nullptr);
  EXPECT_EQ(u->gate_delay_fall->int_val, 3u);
  EXPECT_EQ(u->gate_inst_name, "u1");
  ASSERT_EQ(u->gate_terminals.size(), 3u);  // output_terminal + 2 inputs
}

// §29.8 states a UDP instance name is optional, just as for gates. The
// udp_instance BNF brackets name_of_instance accordingly. This observes the
// nameless form parsing into an anonymous instance with its terminals intact.
TEST(UdpInstantiation, OptionalInstanceName) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_TRUE(insts[0]->gate_inst_name.empty());
  EXPECT_EQ(insts[0]->gate_terminals.size(), 3u);
}

// §29.8 permits an optional range for an array of UDP instances; the
// name_of_instance BNF carries an unpacked_dimension for this. This observes
// the range component being accepted and recorded on the instance.
TEST(UdpInstantiation, ArrayOfInstances) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp u1 [3:0] (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_NE(insts[0]->inst_range_left, nullptr);
  EXPECT_NE(insts[0]->inst_range_right, nullptr);
}

// §29.8 BNF udp_instantiation allows a comma-separated list of udp_instance
// items under one declaration. This observes the list repetition producing
// multiple instances of the same UDP from a single statement.
TEST(UdpInstantiation, MultipleInstancesInOneStatement) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp u1 (y, a, b), u2 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 2u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_EQ(insts[1]->gate_inst_name, "u2");
}

// §29.8 BNF udp_instantiation places the optional drive_strength and delay2
// ahead of the whole comma-separated instance list, so a strength/delay written
// once applies to every instance in the declaration. This observes that the
// pair parsed once is propagated onto both instances of the list.
TEST(UdpInstantiation, SharedStrengthAndDelayAcrossInstances) {
  auto r =
      Parse(std::string(udp_def) +
            "module top;\n"
            "  my_udp (strong0, weak1) #(2, 3) u1 (y, a, b), u2 (y, a, b);\n"
            "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 2u);
  for (auto* u : insts) {
    EXPECT_EQ(u->drive_strength0, 4u);  // strong0
    EXPECT_EQ(u->drive_strength1, 2u);  // weak1
    ASSERT_NE(u->gate_delay, nullptr);
    EXPECT_EQ(u->gate_delay->int_val, 2u);
    ASSERT_NE(u->gate_delay_fall, nullptr);
    EXPECT_EQ(u->gate_delay_fall->int_val, 3u);
  }
}

// §29.8's delay2 permits a single delay as well as a rise/fall pair. This
// observes the lower-bound input form: one delay parses into the rise slot with
// no fall delay recorded, still under the two-delay ceiling.
TEST(UdpInstantiation, SingleDelayForm) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp #5 u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->int_val, 5u);
  EXPECT_EQ(insts[0]->gate_delay_fall, nullptr);
}

// §29.8's own example writes the delay as a single parameter reference
// (d_edge_ff #p3 d_inst (...)), not a literal. This observes that constant-form
// of the delay2 input: a parameter name parses into the rise-delay slot as an
// identifier expression, distinct from the literal forms above.
TEST(UdpInstantiation, ParameterValuedDelay) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  parameter p3 = 12;\n"
                 "  my_udp #p3 u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->kind, ExprKind::kIdentifier);
  EXPECT_EQ(insts[0]->gate_delay->text, "p3");
  EXPECT_EQ(insts[0]->gate_delay_fall, nullptr);
}

// §29.8 limits UDP instances to two delays because z is not supported, so the
// delay specification is delay2 rather than the gate-style delay3. A third
// delay must be rejected.
TEST(UdpInstantiation, RejectsThreeDelays) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp #(1, 2, 3) u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
