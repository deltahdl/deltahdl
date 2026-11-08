#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OperatorOperandTypeElaboration, UnpackedStructOperandOfPlusIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef struct { int a; int b; } st_t;\n"
      "  st_t s = '{1, 2};\n"
      "  int r;\n"
      "  initial r = s + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an unpacked structure or union is not an operand of this operator", 5,
      "11.3"));
}

TEST(OperatorOperandTypeElaboration, UnpackedStructOperandOfUnaryIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  struct { int a; } s;\n"
      "  int r;\n"
      "  initial r = -s;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "an unpacked structure or union is not an operand of this operator", 4,
      "11.3"));
}

TEST(OperatorOperandTypeElaboration, PackedStructOperandAndEqualityAreLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { byte a; byte b; } p_t;\n"
      "  typedef struct { int a; } u_t;\n"
      "  p_t p; u_t s, t2;\n"
      "  int r; bit e;\n"
      "  initial begin r = p + 1; e = (s == t2); end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(OperatorOperandTypeElaboration, TaggedUnionOperandOfMatchesIsLegal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef union tagged { struct { int v; int w; } a; void b; } u_t;\n"
      "  u_t tmp = tagged a '{5, 0};\n"
      "  int val;\n"
      "  initial val = tmp matches tagged a '{.v, 0} ? v : 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
