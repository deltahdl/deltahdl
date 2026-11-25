#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_child_instance.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kInterfaceWithAType =
    "interface ifc; typedef logic [5:0] w6_t; endinterface\n"
    "class K #(type T = int); T v; endclass\n"
    "module c #(parameter type T = int) (); T v; endmodule\n"
    "interface j #(parameter type T = int); endinterface\n";

struct HierarchicalTypeValue {
  std::string_view item;
  std::string_view report;
  std::string_view subclause;
};

constexpr std::string_view kNotAType = "does not name a type";
constexpr std::string_view kNotADataType = "can only be set to a data type";

constexpr HierarchicalTypeValue kHierarchicalTypeValues[] = {
    {"module t; ifc i(); c #(.T(i.w6_t)) u(); endmodule\n", kNotAType,
     "6.20.3"},
    {"module t; ifc i(); c #(i.w6_t) u(); endmodule\n", kNotAType, "6.20.3"},
    {"module t; ifc i(); j #(i.w6_t) jj(); endmodule\n", kNotAType, "6.20.3"},
    {"module t; ifc i(); K #(i.w6_t) k; endmodule\n", kNotAType, "6.20.3"},
    {"module t; ifc i(); localparam type L = i.w6_t; endmodule\n",
     kNotADataType, "6.20.3"},
    {"module t; ifc i(); parameter type P = i.w6_t; endmodule\n", kNotADataType,
     "6.20.3"},
    {("module t; ifc i();\n"
      "  if (1) begin : g localparam type L = i.w6_t; end\n"
      "endmodule\n"),
     kNotADataType, "6.20.3"},
};

TEST(TypeParameterElab, HierarchicalNameAsATypeParameterValueIsReported) {
  for (const auto& value : kHierarchicalTypeValues) {
    std::string src =
        std::string(kInterfaceWithAType) + std::string(value.item);
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(value.report),
                              LineHolding(src, "i.w6_t"),
                              std::string(value.subclause)));
  }
}

TEST(TypeParameterElab, LocalTypeAsATypeParameterValueIsAccepted) {
  for (const auto& value : kHierarchicalTypeValues) {
    std::string src =
        std::string(kInterfaceWithAType) + std::string(value.item);
    for (auto pos = src.find("i.w6_t"); pos != std::string::npos;
         pos = src.find("i.w6_t")) {
      src.replace(pos, 6, "w6_t");
    }
    src.replace(src.find("module t"), 8, "typedef logic [5:0] w6_t;\nmodule t");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

TEST(BodyTypeParameter, DefparamOfABodyTypeParameterIsRejected) {
  ElabFixture e;
  ElaborateSrc(
      "module c;\n"
      "  parameter type T = int;\n"
      "  T x;\n"
      "endmodule\n"
      "module top;\n"
      "  c u();\n"
      "  defparam u.T = 16;\n"
      "endmodule\n",
      e, "top");
  EXPECT_TRUE(ReportedError(e.diag.Diagnostics(),
                            "defparam cannot override a type parameter", 7,
                            "23.10.1"));
}

TEST(BodyTypeParameter, InstanceOverrideOfABodyTypeParameterIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module c;\n"
      "  parameter type T = int;\n"
      "  T x;\n"
      "endmodule\n"
      "module top;\n"
      "  c #(.T(byte)) v();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ExpectVariableWidth(SoleChildInstance(design), "x", 8u);
}

TEST(BodyTypeParameter, SpecializationTakesAPackageTypeAndNoVariable) {
  ElabFixture f;
  ElaborateSrc(
      "package pk; typedef logic [11:0] t; int v; endpackage\n"
      "class X #(type T = int); T v; endclass\n"
      "module top;\n"
      "  int v;\n"
      "  X #(pk::t) a;\n"
      "  X #(.T(pk::t)) b;\n"
      "  X #(v) c;\n"
      "  X #(pk::v) d;\n"
      "  X #(pk::t, pk::t) e;\n"
      "endmodule\n",
      f, "top");
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {5, 6}) EXPECT_FALSE(ErrorOnLine(diags, kLine));
  for (const int kLine : {7, 8}) EXPECT_TRUE(ErrorOnLine(diags, kLine));
  EXPECT_TRUE(ReportedError(diags,
                            "too many positional parameter overrides for "
                            "class 'X': 2 provided, 1 allowed",
                            9, "23.10.2.1"));
}

constexpr std::string_view kEnumRestrictedItems[] = {
    "module t #(type enum T = @) (); endmodule\n",
    "module t; parameter type enum T = @; endmodule\n",
    "module t; if (1) begin : g localparam type enum T = @; end endmodule\n",
    "module t; initial begin localparam type enum T = @; end endmodule\n",
    ("module t;\n"
     "  function void f(); localparam type enum T = @; endfunction\n"
     "endmodule\n"),
    ("interface i; parameter type enum T = @; endinterface\n"
     "module t; i u(); endmodule\n"),
    "program t; parameter type enum T = @; endprogram\n",
    ("class K #(type enum T = @); endclass\n"
     "module t; K #() k; endmodule\n"),
    ("class K; localparam type enum T = @; endclass\n"
     "module t; K k; endmodule\n"),
    ("package p; localparam type enum T = @; endpackage\n"
     "module t; endmodule\n"),
    "parameter type enum T = @;\nmodule t; endmodule\n",
};

std::string WithTypeWritten(std::string_view item, std::string_view type) {
  std::string src(item);
  src.replace(src.find('@'), 1, type);
  return src;
}

TEST(InPlaceTypeParameterElab, StructureForAnEnumerationParameterIsReported) {
  for (const auto& item : kEnumRestrictedItems) {
    std::string src = WithTypeWritten(item, "struct packed { bit a; }");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "type parameter 'T' is assigned a type that does "
                              "not conform to the required enum kind",
                              LineHolding(src, "type enum T"), "6.20.3"));
  }
}

TEST(InPlaceTypeParameterElab, EnumerationForAnEnumerationParameterIsAccepted) {
  for (const auto& item : kEnumRestrictedItems) {
    std::string src = WithTypeWritten(item, "enum { A, B }");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

constexpr std::string_view kEnumDefaultItems[] = {
    "module t #(type T = @) (); endmodule\n",
    "module t; parameter type T = @; endmodule\n",
    "interface i #(type T = @) (); endinterface module t; i u(); endmodule\n",
    ("interface i; localparam type T = @; endinterface\n"
     "module t; i u(); endmodule\n"),
    "program t #(type T = @) (); endprogram\n",
};

TEST(InPlaceTypeParameterElab, EnumerationConstantsWithOneValueAreReported) {
  for (const auto& item : kEnumDefaultItems) {
    std::string src = WithTypeWritten(item, "enum { A = 1, B = 1 }");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "duplicate enum member value 1", 1, "6.19"));
  }
}

TEST(InPlaceTypeParameterElab, EnumerationConstantsOfTheirOwnAreAccepted) {
  for (const auto& item : kEnumDefaultItems) {
    std::string src = WithTypeWritten(item, "enum { A = 1, B = 2 }");
    SCOPED_TRACE(src);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

TEST(InPlaceTypeParameterElab, EnumerationConstantsAreNotNamedOutside) {
  const std::string kSrc =
      "module m #(type T = enum { A, B }) ();\n"
      "  int x = B;\n"
      "endmodule\n"
      "class K #(type T = enum { C, D });\n"
      "  int x = D;\n"
      "endclass\n"
      "module t;\n"
      "  m u();\n"
      "  K #() k;\n"
      "  int y = B;\n"
      "  int z = D;\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(kSrc, f, "t");
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {2, 5}) EXPECT_FALSE(ErrorOnLine(diags, kLine));
  EXPECT_TRUE(ReportedError(diags, "reference to unresolved identifier 'B'", 10,
                            "23.9"));
  EXPECT_TRUE(ReportedError(diags, "reference to unresolved identifier 'D'", 11,
                            "23.9"));
}

TEST(InPlaceTypeParameterElab, IntegerForAnEnumerationVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t #(type T = enum { A, B }) ();\n"
      "  localparam type U = enum { C, D };\n"
      "  T v;\n"
      "  U w;\n"
      "  initial v = B;\n"
      "  initial w = D;\n"
      "  initial v = 1;\n"
      "  initial w = 1;\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {5, 6}) EXPECT_FALSE(ErrorOnLine(diags, kLine));
  for (const int kLine : {7, 8}) EXPECT_TRUE(ErrorOnLine(diags, kLine));
}

}  // namespace
