// §16.13.6: Sequence methods

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.10 Production #28: sequence_method_call
// sequence_method_call ::= sequence_instance . method_identifier
// =============================================================================
TEST(ParserA210, SequenceMethodCall_Triggered) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.triggered |-> c);\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceMethodCall_Matched) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.matched |-> c);\n"
              "endmodule\n"));
}

}  // namespace
