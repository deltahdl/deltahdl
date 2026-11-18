#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

struct OverrideForm {
  const char* where;
  std::string (*instance)(const std::string& value);
};

constexpr OverrideForm kOverrideForms[] = {
    {"a defparam",
     [](const std::string& value) {
       return "  child u();\n  defparam u.P = " + value + ";\n";
     }},
    {"an ordered list",
     [](const std::string& value) {
       return "  child #(" + value + ") u();\n";
     }},
    {"a named list",
     [](const std::string& value) {
       return "  child #(.P(" + value + ")) u();\n";
     }},
};

struct OverrideCase {
  const char* value;
  const char* shown;
  const char* printed;
};

void ExpectEveryOverridePrints(const std::string& decl, const OverrideCase& c) {
  for (const OverrideForm& form : kOverrideForms) {
    SCOPED_TRACE(std::string(form.where) + ", " + c.value + ", " + c.shown);
    SimFixture f;
    std::string src = "module child #(parameter " + decl +
                      ") ();\n"
                      "  initial $display(\"%0d %0d\", $bits(P), " +
                      c.shown +
                      ");\n"
                      "endmodule\n"
                      "module top;\n" +
                      form.instance(c.value) + "endmodule\n";
    EXPECT_EQ(RunCapture(src, f), c.printed);
    EXPECT_EQ(f.diag.ErrorCount(), 0u);
  }
}

TEST(ValueParameterOverride, UntypedUnrangedTakesTheOverridesTypeAndRange) {
  const OverrideCase kCases[] = {
      {"5'd9", "P", "5 9\n"},
      {"8'd3", "P", "8 3\n"},
      {"4'sb1101", "P < 0", "4 1\n"},
      {"2.5", "$rtoi(P * 4)", "64 10\n"},
  };
  for (const OverrideCase& c : kCases) {
    ExpectEveryOverridePrints("P = 13'h7e", c);
  }
}

TEST(ValueParameterOverride, RangedUntypedKeepsItsRangeUnsigned) {
  const OverrideCase kCases[] = {
      {"5'd17", "P", "4 1\n"},
      {"3.7", "P", "4 4\n"},
      {"-1", "P", "4 15\n"},
      {"-1", "P < 0", "4 0\n"},
  };
  for (const OverrideCase& c : kCases) {
    ExpectEveryOverridePrints("[3:0] P = 0", c);
  }
}

TEST(ValueParameterOverride, TypedUnrangedConvertsTheOverrideToItsType) {
  const OverrideCase kCases[] = {
      {"64'h1_0000_0002", "P", "32 2\n"},
      {"3.7", "P", "32 4\n"},
  };
  for (const OverrideCase& c : kCases) {
    ExpectEveryOverridePrints("int P = 0", c);
  }
}

TEST(ValueParameterOverride, SignedUnrangedTakesTheOverridesRange) {
  const OverrideCase kCases[] = {
      {"40'sh80_0000_0001", "P < 0", "40 1\n"},
      {"4'sd5", "P", "4 5\n"},
      {"4'sb1011", "P", "4 -5\n"},
  };
  for (const OverrideCase& c : kCases) {
    ExpectEveryOverridePrints("signed P = 0", c);
  }
}

TEST(ValueParameterOverride, SignedRangedKeepsItsRangeAndSignedness) {
  const OverrideCase kCases[] = {
      {"12", "P", "4 -4\n"},
      {"12", "P < 0", "4 1\n"},
      {"5'd17", "P", "4 1\n"},
      {"12.6", "P", "4 -3\n"},
  };
  for (const OverrideCase& c : kCases) {
    ExpectEveryOverridePrints("signed [3:0] P = 0", c);
  }
}

TEST(TypeParameterOverride, ADependentValueParameterTakesTheNewType) {
  const char* const kInstances[] = {"child #(.T(bit [1:0])) u();",
                                    "child #(bit [1:0]) u();"};
  for (const char* instance : kInstances) {
    SCOPED_TRACE(instance);
    SimFixture f;
    EXPECT_EQ(
        RunCapture(std::string("module child #(parameter type T = int, "
                               "parameter T p3 = 7) ();\n"
                               "  initial $display(\"%0d %0d\", $bits(p3), "
                               "p3);\n"
                               "endmodule\n"
                               "module top;\n  ") +
                       instance + "\nendmodule\n",
                   f),
        "2 3\n");
    EXPECT_EQ(f.diag.ErrorCount(), 0u);
  }
}

TEST(TypeParameterOverride, AnOrderedIntegralTypeReplacesAClassDefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\nendclass\n"
                       "module M #(parameter type T = C, parameter T p = 4) "
                       "();\n"
                       "  initial $display(\"%0d %0d\", $bits(p), p);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  M #(int) u();\n"
                       "endmodule\n",
                       f),
            "32 4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(ValueParameterOverride, BlockAndFunctionParametersFollowAnOverride) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child;\n"
                       "  parameter W = 4;\n"
                       "  function int f;\n"
                       "    parameter R = W + 1;\n"
                       "    return R;\n"
                       "  endfunction\n"
                       "  initial begin : b\n"
                       "    parameter Q = W * 2;\n"
                       "    $display(\"%0d %0d\", Q, f());\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(.W(5)) u();\n"
                       "endmodule\n",
                       f),
            "10 6\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(ValueParameterOverride, OrderedListSkipsABodyLocalparam) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module my_mem;\n"
                       "  parameter addr_width = 16;\n"
                       "  localparam mem_size = 1 << addr_width;\n"
                       "  parameter data_width = 8;\n"
                       "  initial $display(\"%0d %0d %0d\", addr_width, "
                       "data_width, mem_size);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  my_mem #(12, 16) m();\n"
                       "endmodule\n",
                       f),
            "12 16 4096\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(ValueParameterOverride, NamedListInAnyOrderWithAnEmptyEntryFirst) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module child #(parameter size = 4, "
                       "parameter delay = 3) ();\n"
                       "  initial $display(\"%0d %0d\", size, delay);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  child #(.delay( ), .size(10)) u();\n"
                       "endmodule\n",
                       f),
            "10 3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(ValueParameterOverride, OneModuleTakesOrderedAndNamedOnSeparateInstances) {
  SimFixture f;
  std::string out = RunCapture(
      "module child #(parameter A = 1, parameter B = 2) ();\n"
      "  initial $display(\"%m %0d %0d\", A, B);\n"
      "endmodule\n"
      "module top;\n"
      "  child #(5, 6) u1();\n"
      "  child #(.B(8)) u2();\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("top.u1 5 6\n"), std::string::npos);
  EXPECT_NE(out.find("top.u2 1 8\n"), std::string::npos);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
