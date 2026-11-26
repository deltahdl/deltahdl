#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kChildren =
    "module m #(type T = int) (); T x; endmodule\n"
    "interface i #(type T = int) (); T x; endinterface\n";

struct Parent {
  std::string_view open;
  std::string_view close;
};

constexpr Parent kParents[] = {
    {"module top;\n", "endmodule\n"},
    {"interface j;\n", "endinterface\nmodule top; j k(); endmodule\n"},
    {"module top;\n  if (1) begin : g\n", "  end\nendmodule\n"},
};

std::string InParent(const Parent& parent, std::string_view body) {
  std::string text(kChildren);
  text.append(parent.open).append(body).append(parent.close);
  return text;
}

TEST(OverrideEnumerationElaboration, DuplicateValueInAnOverrideIsReported) {
  for (const Parent& parent : kParents) {
    for (std::string_view body : {"  i #(enum {A = 1, B = 1}) w();\n",
                                  "  i #(.T(enum {A = 1, B = 1})) w();\n"}) {
      const std::string kSrc = InParent(parent, body);
      SCOPED_TRACE(kSrc);
      ElabFixture f;
      ElaborateSrc(kSrc, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "duplicate enum member value 1",
                                LineHolding(kSrc, "enum {A = 1"), "6.19"));
    }
  }
}

TEST(OverrideEnumerationElaboration, DistinctValuesInAnOverrideAreAccepted) {
  for (const Parent& parent : kParents) {
    const std::string kSrc =
        InParent(parent, "  i #(enum {A = 1, B = 2}) w();\n  int y = B;\n");
    SCOPED_TRACE(kSrc);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(OverrideEnumerationElaboration, ConstantIsNoNameOfTheInstantiatedModule) {
  const std::string kSrc =
      "module n #(type T = int) ();\n"
      "  T x;\n"
      "  int y = B;\n"
      "endmodule\n"
      "module top;\n"
      "  n #(enum {A, B}) u();\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'B'",
                            LineHolding(kSrc, "int y = B"), "23.9"));
}

constexpr Parent kDeclarationParents[] = {
    {"module top;\n", "endmodule\n"},
    {"interface j;\n", "endinterface\nmodule top; j k(); endmodule\n"},
    {"program q;\n", "endprogram\nmodule top; q k(); endmodule\n"},
    {"module top;\n  if (1) begin : g\n", "  end\nendmodule\n"},
    {"module top;\n  for (genvar n = 0; n < 1; n++) begin : l\n",
     "  end\nendmodule\n"},
};

std::string WithClassX(const Parent& parent, std::string_view body) {
  std::string text = "class X #(type T = int); T v; endclass\n";
  text.append(parent.open).append(body).append(parent.close);
  return text;
}

TEST(SpecializationEnumerationElaboration,
     DuplicateValueInAnArgumentIsReported) {
  for (const Parent& parent : kDeclarationParents) {
    for (std::string_view body :
         {"  X #(enum {A = 1, B = 1}) k;\n",
          "  typedef X #(.T(enum {A = 1, B = 1})) x_t;\n"}) {
      const std::string kSrc = WithClassX(parent, body);
      SCOPED_TRACE(kSrc);
      ElabFixture f;
      ElaborateSrc(kSrc, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "duplicate enum member value 1",
                                LineHolding(kSrc, "enum {A = 1"), "6.19"));
    }
  }
}

TEST(SpecializationEnumerationElaboration, DistinctValuesInAnArgumentAccepted) {
  for (const Parent& parent : kDeclarationParents) {
    const std::string kSrc =
        WithClassX(parent,
                   "  X #(enum {A = 1, B = 2}) k;\n"
                   "  typedef X #(.T(enum {C = 1, D = 2})) x_t;\n"
                   "  int y = B + D;\n");
    SCOPED_TRACE(kSrc);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_FALSE(f.has_errors);
  }
}

TEST(SpecializationEnumerationElaboration, ConstantIsNoNameOfTheClass) {
  const std::string kSrc =
      "class Z #(type T = int);\n"
      "  T v;\n"
      "  function int f(); return B; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  Z #(enum {A, B}) k = new;\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'B'",
                            LineHolding(kSrc, "return B"), "23.9"));
}

TEST(InitializerOperandEnumerationElaboration,
     DuplicateValueInAnOperandIsReported) {
  for (const Parent& parent : kDeclarationParents) {
    for (std::string_view body :
         {"  int w = $bits(enum {A = 1, B = 1});\n",
          "  localparam int P = $bits(type(enum {A = 1, B = 1}));\n",
          "  wire integer z = $bits(enum {A = 1, B = 1});\n"}) {
      const std::string kSrc = InParent(parent, body);
      SCOPED_TRACE(kSrc);
      ElabFixture f;
      ElaborateSrc(kSrc, f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                                "duplicate enum member value 1",
                                LineHolding(kSrc, "enum {A = 1"), "6.19"));
    }
  }
}

TEST(InitializerOperandEnumerationElaboration,
     DistinctValuesInAnOperandAccepted) {
  for (const Parent& parent : kDeclarationParents) {
    const std::string kSrc =
        InParent(parent,
                 "  int w = $bits(enum {A = 1, B = 2});\n"
                 "  localparam int P = $bits(type(enum {C = 1, D = 2}));\n"
                 "  wire integer z = $bits(enum {E = 1, F = 2});\n"
                 "  int y = B + D + F;\n");
    SCOPED_TRACE(kSrc);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_FALSE(f.has_errors);
  }
}

}  // namespace
