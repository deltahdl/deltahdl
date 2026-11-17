#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct Conversion {
  const char* spec;
  const char* text;
  const char* decl;
  const char* show;
  const char* expected;
};

std::string Convert(const std::string& spec, const Conversion& c,
                    SimFixture& f) {
  f.ctx.AddPlusArg(std::string("V=") + c.text);
  return RunCapture(std::string("module t;\n  ") + c.decl +
                        " v;\n"
                        "  initial if ($value$plusargs(\"V=" +
                        spec + "\", v)) $display(\"" + c.show +
                        "\", v);\n"
                        "endmodule\n",
                    f);
}

constexpr Conversion kEveryConversion[] = {
    {"d", "12", "int", "%0d", "12\n"},
    {"o", "17", "int", "%0d", "15\n"},
    {"h", "1f", "int", "%0d", "31\n"},
    {"x", "1f", "int", "%0d", "31\n"},
    {"b", "101", "int", "%0d", "5\n"},
    {"e", "2.5e1", "real", "%0.1f", "25.0\n"},
    {"f", "1.25", "real", "%0.2f", "1.25\n"},
    {"g", "1.5", "real", "%0.1f", "1.5\n"},
    {"s", "ab", "string", "%s", "ab\n"},
};

TEST(ValuePlusargsSpellings, UppercaseFormsConvertLikeLowercase) {
  for (const Conversion& c : kEveryConversion) {
    SimFixture f;
    std::string spec = "%";
    spec += static_cast<char>(c.spec[0] - 'a' + 'A');
    EXPECT_EQ(Convert(spec, c, f), c.expected) << spec;
    EXPECT_FALSE(f.diag.HasErrors()) << spec;
  }
}

TEST(ValuePlusargsSpellings, LeadingZeroFormsConvertLikeTheBareForm) {
  for (const Conversion& c : kEveryConversion) {
    for (bool upper : {false, true}) {
      SimFixture f;
      std::string spec = "%0";
      spec += upper ? static_cast<char>(c.spec[0] - 'a' + 'A') : c.spec[0];
      EXPECT_EQ(Convert(spec, c, f), c.expected) << spec;
      EXPECT_FALSE(f.diag.HasErrors()) << spec;
    }
  }
}

TEST(ValuePlusargsSpellings, DISABLED_AConversionOutsideTheSetIsReported) {
  for (const char* spec : {"%c", "%t", "%v", "%u", "%z", "%m"}) {
    SimFixture f;
    f.ctx.AddPlusArg("CH=a");
    f.ctx.AddPlusArg("N=7");
    std::string out =
        RunCapture(std::string("module t;\n"
                               "  logic [7:0] ch = 8'h11;\n"
                               "  int n;\n"
                               "  initial begin\n"
                               "    void'($value$plusargs(\"CH=") +
                       spec +
                       "\", ch));\n"
                       "    void'($value$plusargs(\"N=%d\", n));\n"
                       "    $display(\"%h %0d\", ch, n);\n"
                       "  end\n"
                       "endmodule\n",
                   f);
    EXPECT_EQ(out, "11 7\n") << spec;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("$value$plusargs: ") + spec +
                                  " is not one of the conversions a user "
                                  "string may name",
                              5, "21.6"))
        << spec;
  }
}

TEST(ValuePlusargsIllegalCharacters, HexAndOctalWriteAllX) {
  for (const Conversion& c :
       {Conversion{"h", "1g", "logic [7:0]", "%b", "xxxxxxxx\n"},
        Conversion{"x", "1g", "logic [7:0]", "%b", "xxxxxxxx\n"},
        Conversion{"o", "19", "logic [7:0]", "%b", "xxxxxxxx\n"}}) {
    SimFixture f;
    EXPECT_EQ(Convert(std::string("%") + c.spec, c, f), c.expected) << c.spec;
  }
}

TEST(ValuePlusargsIllegalCharacters, RealConversionsWriteTheRealOfBx) {
  for (const char* spec : {"%f", "%e", "%g"}) {
    SimFixture f;
    f.ctx.AddPlusArg("R=abc");
    std::string out =
        RunCapture(std::string("module t;\n"
                               "  real r = 7.5;\n"
                               "  initial if ($value$plusargs(\"R=") +
                       spec +
                       "\", r)) $display(\"%0.1f\", r);\n"
                       "endmodule\n",
                   f);
    EXPECT_EQ(out, "0.0\n") << spec;
  }
}

TEST(ValuePlusargsSizing, DISABLED_StringRemainderKeepsItsRightmostCharacters) {
  SimFixture f;
  EXPECT_EQ(Convert("%s", {"s", "abcd", "logic [15:0]", "%h", "6364\n"}, f),
            "6364\n");
}

TEST(ValuePlusargsSizing, NegativeValueFillsAVectorWiderThan32Bits) {
  SimFixture f;
  EXPECT_EQ(Convert("%d", {"d", "-1", "logic [63:0]", "%h", ""}, f),
            "ffffffffffffffff\n");
}

TEST(ValuePlusargsEmptyRemainder, RealConversionsStoreZero) {
  for (const char* spec : {"%f", "%e", "%g"}) {
    SimFixture f;
    f.ctx.AddPlusArg("R=");
    std::string out =
        RunCapture(std::string("module t;\n"
                               "  real r = 7.5;\n"
                               "  initial if ($value$plusargs(\"R=") +
                       spec +
                       "\", r)) $display(\"%0.1f\", r);\n"
                       "endmodule\n",
                   f);
    EXPECT_EQ(out, "0.0\n") << spec;
  }
}

TEST(ValuePlusargsEmptyRemainder, StringConversionIntoAVectorStoresZero) {
  SimFixture f;
  f.ctx.AddPlusArg("S=");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [63:0] v = '1;\n"
      "  initial if ($value$plusargs(\"S=%s\", v)) $display(\"%h\", v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0000000000000000\n");
}

TEST(ValuePlusargsDestinations, DISABLED_RealConversionRoundsIntoAnInt) {
  SimFixture f;
  EXPECT_EQ(Convert("%f", {"f", "2.75", "int", "%0d", ""}, f), "3\n");
}

TEST(ValuePlusargsDestinations, DISABLED_IntegerConversionIntoAReal) {
  SimFixture f;
  EXPECT_EQ(Convert("%d", {"d", "3", "real", "%0.1f", ""}, f), "3.0\n");
}

TEST(ValuePlusargsDestinations,
     DISABLED_ClassPropertiesInAMethodAndThroughAHandle) {
  SimFixture f;
  f.ctx.AddPlusArg("N=41");
  f.ctx.AddPlusArg("S=hi");
  std::string out = RunCapture(
      "class C;\n"
      "  int n;\n"
      "  string s;\n"
      "  function void get();\n"
      "    void'($value$plusargs(\"N=%d\", n));\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    c.get();\n"
      "    void'($value$plusargs(\"S=%s\", c.s));\n"
      "    $display(\"%0d %s\", c.n, c.s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "41 hi\n");
}

TEST(ValuePlusargsUserStringSim, ParameterConstantUserStringConverts) {
  SimFixture f;
  f.ctx.AddPlusArg("N=9");
  std::string out = RunCapture(
      "module t;\n"
      "  parameter P = \"N=%d\";\n"
      "  int v;\n"
      "  initial if ($value$plusargs(P, v)) $display(\"%0d\", v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "9\n");
}

}  // namespace
