// §28.5: buf and not gates

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.3.1 Production #1: gate_instantiation (n_output_gatetype alternative)
// gate_instantiation ::=
//   n_output_gatetype [drive_strength] [delay2] n_output_gate_instance
//                     {, n_output_gate_instance} ;
// =============================================================================
TEST(ParserA301, GateInst_BufBasic) {
  auto r = Parse(
      "module m;\n"
      "  buf (out, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 2u);
}

}  // namespace
