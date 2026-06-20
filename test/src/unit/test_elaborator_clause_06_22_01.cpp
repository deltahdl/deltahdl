#include "fixture_elaborator.h"

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

}  // namespace
