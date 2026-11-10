#include <gtest/gtest.h>

#include <cstdint>
#include <format>
#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_param_value.h"
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

TEST(MatchingTypesElaboration, TypesEachInterfaceInstanceDeclaresAreDistinct) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc;\n"
      "  typedef enum {X, Y} e_t;\n"
      "  e_t e;\n"
      "  int n;\n"
      "endinterface\n"
      "module top();\n"
      "  ifc i1 ();\n"
      "  ifc i2 ();\n"
      "  initial begin\n"
      "    i1.e = i2.e;\n"
      "    i1.n = i2.n;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'i1.e' and 'i2.e' have types the instances 'i1' "
                            "and 'i2' each declare for themselves, which are "
                            "distinct types",
                            10, "6.22"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "each declare for themselves", 11, "6.22"));
}

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

struct TypeComparison {
  std::string_view name;
  std::string_view left;
  std::string_view right;
  int64_t matches;
};

void ExpectComparisons(std::string_view before_module,
                       std::string_view declarations,
                       std::initializer_list<TypeComparison> comparisons) {
  std::string src =
      std::string(before_module) + "module m;\n" + std::string(declarations);
  for (const auto& c : comparisons) {
    src += std::format("  localparam bit {} = type({}) == type({});\n", c.name,
                       c.left, c.right);
  }
  src += "endmodule\n";
  ElabFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (const auto& c : comparisons) {
    SCOPED_TRACE(c.name);
    EXPECT_EQ(ParamValue(design, c.name), c.matches);
  }
}

TEST(MatchingTypeComparison, BuiltInTypeMatchesOnlyItself) {
  ExpectComparisons("", "",
                    {{"kInt", "int", "int", 1},
                     {"kIntInteger", "int", "integer", 0},
                     {"kReal", "real", "real", 1},
                     {"kRealShortreal", "real", "shortreal", 0},
                     {"kString", "string", "string", 1},
                     {"kStringChandle", "string", "chandle", 0}});
}

TEST(MatchingTypeComparison, RenamingTypedefMatchesWhatItRenames) {
  ExpectComparisons("typedef bit node;\n",
                    "  typedef node type2;\n"
                    "  typedef logic [3:0] nib_t;\n",
                    {{"kNode", "node", "bit", 1},
                     {"kType2", "type2", "bit", 1},
                     {"kType2Node", "type2", "node", 1},
                     {"kNodeLogic", "node", "logic", 0},
                     {"kNib", "nib_t", "logic [3:0]", 1},
                     {"kNibReversed", "nib_t", "logic [0:3]", 0}});
}

TEST(MatchingTypeComparison, AnonymousTypeMatchesOnlyItsOwnStatement) {
  ExpectComparisons("",
                    "  struct packed {int A; int B;} AB1, AB2;\n"
                    "  struct packed {int A; int B;} AB3;\n"
                    "  enum {E0, E1} EN1, EN2;\n"
                    "  enum {F0, F1} EN3;\n"
                    "  union packed {int A; bit [31:0] B;} U1, U2;\n"
                    "  union packed {int A; bit [31:0] B;} U3;\n",
                    {{"kStructSame", "AB1", "AB2", 1},
                     {"kStructOther", "AB1", "AB3", 0},
                     {"kEnumSame", "EN1", "EN2", 1},
                     {"kEnumOther", "EN1", "EN3", 0},
                     {"kUnionSame", "U1", "U2", 1},
                     {"kUnionOther", "U1", "U3", 0}});
}

TEST(MatchingTypeComparison, NamedUserTypeMatchesOnlyItsOwnObjects) {
  ExpectComparisons("",
                    "  typedef struct packed {int A; int B;} AB_t;\n"
                    "  typedef struct packed {int A; int B;} otherAB_t;\n"
                    "  typedef enum {R, G} col_t;\n"
                    "  typedef enum {R2, G2} col2_t;\n"
                    "  typedef union packed {int A;} un_t;\n"
                    "  typedef union packed {int A;} un2_t;\n"
                    "  class C1; int a; endclass\n"
                    "  class C2; int a; endclass\n"
                    "  AB_t AB1; AB_t AB2;\n"
                    "  otherAB_t AB3;\n"
                    "  col_t c1;\n"
                    "  un_t u1;\n"
                    "  C1 h1;\n",
                    {{"kStructObjects", "AB1", "AB2", 1},
                     {"kStructTypedef", "AB1", "AB_t", 1},
                     {"kStructOther", "AB3", "AB1", 0},
                     {"kEnum", "c1", "col_t", 1},
                     {"kEnumOther", "c1", "col2_t", 0},
                     {"kUnion", "u1", "un_t", 1},
                     {"kUnionOther", "u1", "un2_t", 0},
                     {"kClass", "h1", "C1", 1},
                     {"kClassOther", "C1", "C2", 0}});
}

TEST(MatchingTypeComparison, BitVectorMatchesTheWidthedTypeItSpellsOut) {
  ExpectComparisons("",
                    "  typedef bit signed [7:0] BYTE;\n"
                    "  typedef bit signed [0:7] ETYB;\n",
                    {{"kByte", "BYTE", "byte", 1},
                     {"kEtyb", "ETYB", "byte", 0},
                     {"kInt", "bit signed [31:0]", "int", 1},
                     {"kIntUnsigned", "bit [31:0]", "int", 0},
                     {"kShortint", "bit signed [15:0]", "shortint", 1},
                     {"kLongint", "bit signed [63:0]", "longint", 1},
                     {"kInteger", "logic signed [31:0]", "integer", 1},
                     {"kIntegerTwoState", "bit signed [31:0]", "integer", 0},
                     {"kIntegerUnsigned", "logic [31:0]", "integer", 0},
                     {"kTime", "logic [63:0]", "time", 1},
                     {"kTimeWidth", "logic [62:0]", "time", 0}});
}

TEST(MatchingTypeComparison, ArraysMatchByKindBoundsIndexAndElement) {
  ExpectComparisons("",
                    "  typedef byte MEM_BYTES [256];\n"
                    "  typedef bit signed [7:0] MY_MEM_BYTES [256];\n"
                    "  typedef logic [1:0][3:0] NIBBLES;\n"
                    "  typedef logic [7:0] MY_BYTE;\n"
                    "  typedef logic MD_ARY [][2:0];\n"
                    "  typedef logic MD_ARY_TOO [][0:2];\n"
                    "  typedef int FA [0:3];\n"
                    "  typedef int FB [1:4];\n"
                    "  typedef int FC [0:3];\n"
                    "  typedef int FD [4];\n"
                    "  typedef int DA [];\n"
                    "  typedef int DB [];\n"
                    "  typedef int QA [$];\n"
                    "  typedef int AS [string];\n"
                    "  typedef int AS2 [string];\n"
                    "  typedef int AI [int];\n"
                    "  typedef bit [7:0] PK;\n"
                    "  typedef bit UP [7:0];\n",
                    {{"kMemBytes", "MEM_BYTES", "MY_MEM_BYTES", 1},
                     {"kNibbles", "NIBBLES", "MY_BYTE", 0},
                     {"kMdAry", "MD_ARY", "MD_ARY_TOO", 0},
                     {"kSameBounds", "FA", "FC", 1},
                     {"kShiftedBounds", "FA", "FB", 0},
                     {"kSizeForm", "FA", "FD", 1},
                     {"kDynamic", "DA", "DB", 1},
                     {"kDynamicQueue", "DA", "QA", 0},
                     {"kAssocIndex", "AS", "AS2", 1},
                     {"kAssocOtherIndex", "AS", "AI", 0},
                     {"kPackedUnpacked", "PK", "UP", 0}});
}

TEST(MatchingTypeComparison, DefaultSigningSpelledOutMatches) {
  ExpectComparisons("",
                    "  typedef byte signed MY_CHAR;\n"
                    "  typedef byte unsigned MY_UCHAR;\n"
                    "  typedef logic unsigned [3:0] LU4;\n",
                    {{"kByteSigned", "MY_CHAR", "byte", 1},
                     {"kByteUnsigned", "MY_UCHAR", "byte", 0},
                     {"kLogicUnsigned", "LU4", "logic [3:0]", 1},
                     {"kIntSigned", "int signed", "int", 1},
                     {"kIntUnsigned", "int unsigned", "int", 0},
                     {"kIntegerSigned", "integer signed", "integer", 1},
                     {"kBitUnsigned", "bit unsigned", "bit", 1},
                     {"kBitSigned", "bit signed", "bit", 0}});
}

TEST(MatchingTypeComparison, PackageTypeMatchesItselfWhereverImported) {
  ExpectComparisons(
      "package p;\n"
      "  typedef struct packed {int A;} pt;\n"
      "  typedef enum {PA, PB} pe;\n"
      "  class PC; endclass\n"
      "endpackage\n"
      "package r;\n"
      "  typedef struct packed {int A;} pt;\n"
      "endpackage\n",
      "  import p::pt;\n"
      "  import p::*;\n"
      "  pt pv;\n"
      "  pe ev;\n"
      "  PC hv;\n",
      {{"kStruct", "pt", "p::pt", 1},
       {"kStructObject", "pv", "p::pt", 1},
       {"kEnum", "ev", "p::pe", 1},
       {"kClass", "hv", "p::PC", 1},
       {"kOtherPackage", "pt", "r::pt", 0}});
}

}  // namespace
