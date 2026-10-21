

#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <string_view>
#include <utility>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeElaboration, IntegerVectorTypeLogic) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, IntegerAtomTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b;\n"
      "  shortint s;\n"
      "  int i;\n"
      "  longint l;\n"
      "  integer n;\n"
      "  time t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, NonIntegerTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  shortreal s;\n"
      "  realtime t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, NetTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  tri t;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "  uwire u;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, SigningExplicitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic signed   [7:0] s;\n"
      "  integer unsigned u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, StructUnionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, UnionTaggedElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int v; void none; } u_t;\n"
      "  u_t u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, StringChandleEventElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  chandle h;\n"
      "  event e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, VarDataTypeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input var int x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, StructMemberAttributeInstanceCrossLink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed {\n"
      "    (* keep *) logic [3:0] a;\n"
      "    logic [3:0] b;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration,
     PackedDimensionConstantExpressionCrossLink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter N = 8;\n"
      "  logic [N-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, TypeReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      // §6.23: a type_reference used in a variable declaration shall be
      // preceded by the 'var' keyword.
      "  var type(x) y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, EnumBaseTypeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum logic [2:0] { A = 0, B = 1, C = 4 } e_t;\n"
      "  e_t x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, EnumNameRangeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum bit [1:0] { S[3] } e_t;\n"
      "  e_t x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, ConstDeclarationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  const int W = 8;\n"
      "  logic [W-1:0] data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// A.2.2.1's package_scope includes `$unit ::`, through which §3.12.1 names a
// compilation-unit declaration a local one hides: m's own T is a byte, and
// `$unit::T a` is the unit's 4-bit T all the same, as `$unit::C::U b` is the
// int the unit's class C declares (#7595).
TEST(NetAndVariableTypeElaboration, TypeNamedThroughTheUnitScopeIsTheUnits) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef logic [3:0] T;\n"
      "class C;\n"
      "  typedef int U;\n"
      "endclass\n"
      "module m;\n"
      "  typedef byte T;\n"
      "  $unit::T a;\n"
      "  $unit::C::U b;\n"
      "  T c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  for (const auto& [name, width] :
       {std::pair<std::string_view, uint32_t>{"a", 4}, {"b", 32}, {"c", 8}}) {
    const RtlirVariable* var = FindVar(design, "m", name);
    ASSERT_NE(var, nullptr) << name;
    EXPECT_EQ(var->width, width) << name;
  }
}

// A nettype's data type named through `$unit ::` is judged as the compilation
// unit's type: §6.6.7 bars a class and a dynamic array from a nettype, and the
// unit's C and DA are those, whatever a module would name C or DA (#7595).
TEST(NetAndVariableTypeElaboration, NettypeOfAUnitClassOrDynamicArrayRejected) {
  ElabFixture f;
  Elaborate(
      "class C;\n"
      "endclass\n"
      "typedef real DA[];\n"
      "module m;\n"
      "  nettype $unit::C nc;\n"
      "  nettype $unit::DA nd;\n"
      "endmodule\n",
      f);
  for (const auto& [name, line] :
       {std::pair<std::string_view, int>{"nc", 5}, {"nd", 6}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::format("data type of user-defined nettype "
                                          "'{}' is not a legal nettype data "
                                          "type",
                                          name),
                              line, "6.6.7"));
  }
}

}  // namespace
