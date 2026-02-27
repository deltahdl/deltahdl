// §16.8.2: Local variable formal arguments in sequence declarations

#include "fixture_parser.h"

using namespace delta;

  return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Productions #22-#23: sequence_port_list, sequence_port_item
// sequence_port_item ::=
//     { attribute_instance } [ local [ sequence_lvar_port_direction ] ]
//     sequence_formal_type formal_port_identifier { variable_dimension }
//     [ = sequence_actual_arg ]
// =============================================================================
TEST(ParserA210, SequencePortItem_LocalInout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local inout int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #24: sequence_lvar_port_direction
// sequence_lvar_port_direction ::= input | inout | output
// =============================================================================
TEST(ParserA210, SequenceLvarPortDirection_Input) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local input int x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceLvarPortDirection_Output) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local output int x);\n"
              "    (1, x = a) ##1 (1, x = b);\n"
              "  endsequence\n"
              "endmodule\n"));
}

}  // namespace
