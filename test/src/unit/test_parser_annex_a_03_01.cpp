// Annex A.3.1: Primitive instantiation and instances

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA303, OutputTerminal_MultipleOutputs) {
  // Multiple output_terminals in n-output gate
  auto r = Parse(
      "module m;\n"
      "  buf (o1, o2, o3, in);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* g = FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf);
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->gate_terminals.size(), 4u);
}

}  // namespace
