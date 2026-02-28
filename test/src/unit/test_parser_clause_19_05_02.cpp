// §19.5.2: Specifying bins for transitions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, BinsOrOptions_DefaultSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins others = default sequence;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #12: trans_list
// =============================================================================
TEST(ParserA211, TransList_Single) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 2);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransList_Multiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 2), (3 => 4);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #13: trans_set
// =============================================================================
TEST(ParserA211, TransSet_SingleRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 3);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransSet_MultipleRanges) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 3 => 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #14: trans_range_list
// =============================================================================
TEST(ParserA211, TransRangeList_SimpleItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (0 => 1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransRangeList_ConsecutiveRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [* 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransRangeList_GotoRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [-> 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransRangeList_NonConsecutiveRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [= 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #15: trans_item (alias for covergroup_range_list)
// =============================================================================
TEST(ParserA211, TransItem_SingleValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (5 => 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, TransItem_MultipleValues) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1, 2, 3 => 4, 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
