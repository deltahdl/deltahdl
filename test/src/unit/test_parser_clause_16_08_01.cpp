#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(AssertionDeclParsing, SequenceFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(sequence sub_seq);\n"
              "    sub_seq ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceFormalType_Untyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(untyped x);\n"
              "    x ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceFormalType_DataType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

}  // namespace
