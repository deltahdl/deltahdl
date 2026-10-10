#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <initializer_list>
#include <string_view>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(MatchingTypesElaboration, MatchingTypesSameTypedef) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t a;\n"
      "  byte_t b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(MatchingTypesElaboration, AnonymousStructSameDeclElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  struct packed {int A; int B;} x, y;\n"
      "  initial x = y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(MatchingTypesElaboration, TypedefEnumAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t a;\n"
      "  color_t b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(MatchingTypesElaboration, ByteSignedMatchesByteElaborates) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  byte b1;\n"
             "  byte signed b2;\n"
             "  initial b1 = b2;\n"
             "endmodule\n"));
}

TEST(MatchingTypesElaboration, PackageTypedefImportElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::byte_t;\n"
      "  byte_t a;\n"
      "  byte_t b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(MatchingTypesElaboration, BuiltinIntMatchesAcrossScopes) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child;\n"
      "  int x;\n"
      "endmodule\n"
      "module top;\n"
      "  int x;\n"
      "  child c();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(MatchingTypesElaboration, SimpleTypedefMatchesUnderlyingBuiltin) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef bit node;\n"
      "  bit b1;\n"
      "  node b2;\n"
      "  initial b1 = b2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.1(c): an anonymous enum type matches itself among data objects
// declared in the same declaration statement, so x and y are assignable.
TEST(MatchingTypesElaboration, AnonymousEnumSameDeclAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  enum {A, B} x, y;\n"
      "  initial x = y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22.1(c): an anonymous union type likewise matches itself among data
// objects of the same declaration statement.
TEST(MatchingTypesElaboration, AnonymousUnionSameDeclAssignmentElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  union packed { logic [7:0] a; logic [7:0] b; } x, y;\n"
      "  initial x = y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.22: a type declared inside a module is a type of each instance's own, so
// the example's s1.v5 = s2.v5 assigns between two distinct unpacked structure
// types, as do the same assignment of an in-place structure or union, an
// enumeration or a class each instance declares. The example's other four
// assignments share a type, through a package, the compilation unit, a type
// parameter the parent overrides, or `int`, and a packed structure is
// equivalent to its counterpart, so none of those is reported, nor is an
// assignment within one instance or one not between two instances' variables.
TEST(MatchingTypesElaboration, TypesEachInstanceDeclaresAreDistinct) {
  ElabFixture f;
  ElaborateSrc(
      "package p1;\n"
      "  typedef struct {int A;} t_1;\n"
      "endpackage\n"
      "typedef struct {int A;} t_2;\n"
      "module sub();\n"
      "  import p1::t_1;\n"
      "  parameter type t_3 = int;\n"
      "  parameter type t_4 = int;\n"
      "  typedef struct {int A;} t_5;\n"
      "  typedef enum {X, Y} t_7;\n"
      "  typedef struct packed {int A;} t_8;\n"
      "  class C;\n"
      "  endclass\n"
      "  t_1 v1;\n"
      "  t_2 v2;\n"
      "  t_3 v3;\n"
      "  t_4 v4;\n"
      "  t_5 v5;\n"
      "  t_7 v7;\n"
      "  t_8 v8;\n"
      "  C v9;\n"
      "  struct {int A;} v10;\n"
      "  union {int A;} v11;\n"
      "  p1::t_1 v12;\n"
      "  int v13;\n"
      "  wire w;\n"
      "endmodule\n"
      "module top();\n"
      "  typedef struct {int A;} t_6;\n"
      "  typedef struct {int v5;} w_t;\n"
      "  w_t st;\n"
      "  sub #(.t_3(t_6)) s1 ();\n"
      "  sub #(.t_3(t_6)) s2 ();\n"
      "  assign s1.v10 = s2.v10;\n"
      "  initial begin\n"
      "    s1.v1 = s2.v1;\n"
      "    s1.v2 = s2.v2;\n"
      "    s1.v3 = s2.v3;\n"
      "    s1.v4 = s2.v4;\n"
      "    s1.v5 = s2.v5;\n"
      "    s1.v7 = s2.v7;\n"
      "    s1.v8 = s2.v8;\n"
      "    s1.v9 = s2.v9;\n"
      "    s1.v11 <= s2.v11;\n"
      "    s1.v12 = s2.v12;\n"
      "    s1.v13 = s2.v13;\n"
      "    s1.v5 = s1.v5;\n"
      "    s1.v5.A = st.v5;\n"
      "    st.v5 = s2.v13;\n"
      "    s1.w = s2.w;\n"
      "    s1.v13 = 5;\n"
      "    s1.v5 = s2.v13;\n"
      "  end\n"
      "endmodule\n",
      f);
  const std::pair<uint32_t, std::string_view> kAssigns[] = {
      {34, "v10"}, {40, "v5"}, {41, "v7"}, {43, "v9"}, {44, "v11"}};
  for (const auto& [line, var] : kAssigns) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::format("'s1.{0}' and 's2.{0}' have types the instances 's1' and "
                    "'s2' each declare for themselves, which are distinct "
                    "types",
                    var),
        line, "6.22"));
  }
  for (uint32_t line :
       {36U, 37U, 38U, 39U, 42U, 45U, 46U, 47U, 48U, 49U, 50U, 51U, 52U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "each declare for themselves", line, "6.22"));
  }
}

// The instances' module is found wherever the compilation unit declares it,
// after the module instantiating it too, and a value a package names is no
// instance's variable.
TEST(MatchingTypesElaboration, InstanceOfALaterModuleIsJudged) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  parameter int k = 1;\n"
      "endpackage\n"
      "module top();\n"
      "  sub s1 ();\n"
      "  sub s2 ();\n"
      "  initial begin\n"
      "    s1.n = p::k;\n"
      "    s1.e = s2.e;\n"
      "  end\n"
      "endmodule\n"
      "module sub();\n"
      "  typedef enum {X, Y} e_t;\n"
      "  e_t e;\n"
      "  int n;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'s1.e' and 's2.e' have types the instances 's1' "
                            "and 's2' each declare for themselves, which are "
                            "distinct types",
                            9, "6.22"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "each declare for themselves", 8, "6.22"));
}

// Instances of a module the compilation unit does not declare have no
// declarations to judge, so an assignment between their variables is left to
// the report of the unknown module.
TEST(MatchingTypesElaboration, InstancesOfAnUndeclaredModuleAreNotJudged) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  missing m1 ();\n"
      "  missing m2 ();\n"
      "  initial m1.x = m2.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unknown module 'missing'", 2,
                            "23.3.2"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "each declare for themselves", 4, "6.22"));
}

}  // namespace
