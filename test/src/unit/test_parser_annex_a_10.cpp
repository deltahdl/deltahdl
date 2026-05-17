#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(BnfClarificationParsing, AutomaticInProceduralBlockOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    automatic int x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, MatchesPrecedenceOverLogicalAnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    if (x matches 1 && y matches 2)\n"
              "      $display(\"ok\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, EventExprInParensOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  event e1, e2;\n"
              "  initial @(e1 or e2) $display(\"ok\");\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, EmptyUnpackedArrayConcat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q = {};\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, TaskCallWithoutParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task; endtask\n"
              "  initial my_task;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, VoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function void my_func(); endfunction\n"
              "  initial my_func();\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, DollarInQueueSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial q[$] = 5;\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, ErrorRandAndRandc) {
  auto r = Parse(
      "class c;\n"
      "  rand randc int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BnfClarificationParsing, ErrorDuplicateRand) {
  auto r = Parse(
      "class c;\n"
      "  rand rand int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BnfClarificationParsing, ErrorDuplicateStatic) {
  auto r = Parse(
      "class c;\n"
      "  static static int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(BnfClarificationParsing, NonvoidFunctionCallWithParens) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function int my_func(); return 0; endfunction\n"
              "  int y;\n"
              "  initial y = my_func();\n"
              "endmodule\n"));
}

TEST(BnfClarificationParsing, CovergroupExtendsInClassOk) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  int val;\n"
              "  covergroup base_cg;\n"
              "    coverpoint val;\n"
              "  endgroup\n"
              "endclass\n"));
}

TEST(BnfClarificationParsing, PureVirtualMethodOk) {
  EXPECT_TRUE(
      ParseOk("virtual class c;\n"
              "  pure virtual function void do_it();\n"
              "endclass\n"));
}

}
