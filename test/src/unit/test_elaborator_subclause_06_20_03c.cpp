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
     "23.10.2"},
    {"module t; ifc i(); c #(i.w6_t) u(); endmodule\n", kNotAType, "23.10.2"},
    {"module t; ifc i(); j #(i.w6_t) jj(); endmodule\n", kNotAType, "23.10.2"},
    {"module t; ifc i(); K #(i.w6_t) k; endmodule\n",
     "parameter override is not a constant expression", "23.10.2"},
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

}  // namespace
