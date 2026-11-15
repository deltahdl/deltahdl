#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CheckerVariables, RandQualifierMarksCheckerVariable) {
  auto r = Parse(
      "checker chk;\n"
      "  rand bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool saw_rand = false;
  for (const auto* item : r.cu->checkers[0]->items) {
    if (item->is_rand) saw_rand = true;
  }
  EXPECT_TRUE(saw_rand);
}

TEST(CheckerVariables, PlainCheckerVariableIsNotRand) {
  auto r = Parse(
      "checker chk;\n"
      "  bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  for (const auto* item : r.cu->checkers[0]->items) {
    EXPECT_FALSE(item->is_rand);
  }
}

TEST(CheckerVariables, ConstFreeVariableParses) {
  EXPECT_TRUE(
      ParseOk("checker chk;\n"
              "  rand const bit [5:0] idx;\n"
              "endchecker\n"));
}

TEST(CheckerVariables, AutomaticCheckerVariableIsIllegal) {
  auto r = Parse(
      "checker chk;\n"
      "  automatic bit flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags,
                            "'automatic' is not allowed in a data_declaration "
                            "outside a procedural context",
                            2, "6.8"));
}

const char* const kAutomatic =
    "'automatic' is not allowed in a data_declaration outside a procedural "
    "context";

void ExpectLifetimes(const std::string& src) {
  auto r = Parse(src);
  for (uint32_t line : LinesHolding(src, "a_bad")) {
    EXPECT_TRUE(ReportedError(r.diags, kAutomatic, line, "6.8")) << line;
  }
  for (uint32_t line : LinesHolding(src, "s_ok")) {
    EXPECT_FALSE(ErrorOnLine(r.diags, line)) << line;
  }
}

TEST(CheckerVariableLifetime, EachAutomaticFormInTheBodyIsReported) {
  ExpectLifetimes(
      "checker chk;\n"
      "  automatic bit a_bad1 = 1'b1;\n"
      "  var automatic logic [3:0] a_bad2;\n"
      "  rand automatic bit a_bad3;\n"
      "  rand const automatic bit a_bad4;\n"
      "  static bit s_ok1;\n"
      "  var static logic [3:0] s_ok2;\n"
      "  rand static bit s_ok3;\n"
      "  bit s_ok4 = 1'b1;\n"
      "endchecker\n");
}

TEST(CheckerVariableLifetime, EachCheckerGenerateBlockIsChecked) {
  ExpectLifetimes(
      "checker chk;\n"
      "  if (1) begin : g\n"
      "    automatic bit a_bad1;\n"
      "    static bit s_ok1;\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : k\n"
      "      automatic bit a_bad2;\n"
      "      static bit s_ok2;\n"
      "    end\n"
      "  endcase\n"
      "  for (genvar i = 0; i < 2; i++) begin : h\n"
      "    automatic bit a_bad3;\n"
      "    static bit s_ok3;\n"
      "  end\n"
      "endchecker\n");
}

TEST(CheckerVariableLifetime, ACheckerInEachEnclosingScopeIsChecked) {
  ExpectLifetimes(
      "module m;\n"
      "  checker c1;\n"
      "    automatic bit a_bad1;\n"
      "    bit s_ok1;\n"
      "  endchecker\n"
      "endmodule\n"
      "package p;\n"
      "  checker c2;\n"
      "    automatic bit a_bad2;\n"
      "    bit s_ok2;\n"
      "  endchecker\n"
      "endpackage\n"
      "checker outer;\n"
      "  checker c3;\n"
      "    automatic bit a_bad3;\n"
      "    bit s_ok3;\n"
      "  endchecker\n"
      "endchecker\n");
}

const char* const kRand = "only a checker's data declaration opens with rand";

TEST(CheckerFreeVariablePlaces, RandInAModuleGenerateBlockIsReported) {
  const std::string kSrc =
      "module m;\n"
      "  if (1) begin : g\n"
      "    rand bit r;\n"
      "    bit b;\n"
      "  end\n"
      "endmodule\n";
  auto r = Parse(kSrc);
  EXPECT_TRUE(ReportedError(r.diags, kRand, 3, "A.1.8"));
  EXPECT_FALSE(ErrorOnLine(r.diags, 4));
}

TEST(CheckerFreeVariablePlaces, RandInACheckersSubroutineOrBlockIsReported) {
  const std::string kSrc =
      "checker chk;\n"
      "  function int f();\n"
      "    rand bit r1;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  function int g();\n"
      "    bit b1;\n"
      "    return 0;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    rand bit r3;\n"
      "  end\n"
      "endchecker\n";
  auto r = Parse(kSrc);
  for (const char* name : {"r1", "r3"}) {
    EXPECT_TRUE(ErrorOnLine(r.diags, LineHolding(kSrc, name))) << name;
  }
  EXPECT_FALSE(ErrorOnLine(r.diags, LineHolding(kSrc, "b1")));
}

}  // namespace
