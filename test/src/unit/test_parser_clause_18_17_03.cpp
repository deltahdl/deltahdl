// §18.17.3: Case production statements

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Case item with default
TEST(ParserA612, RsCaseItemDefault) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (99)\n"
      "               0: a;\n"
      "               default: b;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Default with colon (default :)
TEST(ParserA612, RsCaseItemDefaultColon) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (0)\n"
      "               default : a;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// rs_prod as rs_case
TEST(ParserA612, RsProdAsCase) {
  auto r = Parse(
      "module m;\n"
      "  int sel = 1;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (sel) 0: a; 1: b; default: c; endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_case
// =============================================================================
// Case with multiple items
TEST(ParserA612, RsCaseMultipleItems) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (1)\n"
      "               0: a;\n"
      "               1: b;\n"
      "               2: c;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "      c : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.6.12 Randsequence — rs_case_item
// =============================================================================
// Case item with comma-separated expressions
TEST(ParserA612, RsCaseItemCommaSeparated) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : case (1)\n"
      "               0, 1: a;\n"
      "               2, 3: b;\n"
      "             endcase;\n"
      "      a : { ; };\n"
      "      b : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
