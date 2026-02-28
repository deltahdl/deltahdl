// §16.8.1: Typed formal arguments in sequence declarations

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

// =============================================================================
// §A.2.10 Production #25: sequence_formal_type
// sequence_formal_type ::= data_type_or_implicit | sequence | untyped
// =============================================================================
TEST(ParserA210, SequenceFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(sequence sub_seq);\n"
              "    sub_seq ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceFormalType_Untyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(untyped x);\n"
              "    x ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceFormalType_DataType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

}  // namespace
