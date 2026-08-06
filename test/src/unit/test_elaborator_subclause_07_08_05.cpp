#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayRealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[real];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UserDefinedTypeAssocArrayElaboration, AssocArrayShortrealIndex_Rejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[shortreal];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(UserDefinedTypeAssocArrayElaboration, EnumTypedefIndexAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  int aa[color_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §7.8.5: equality is defined for a composite (struct) type and for the
// dynamically sized types it may contain, so such a type is a legal index.
// This mirrors the clause's own example of a struct holding an unsized
// dynamic-array member used as the index type.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructIndexWithDynamicMemberAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef struct {byte B; int I[*];} unpkt_t;\n"
      "  int aa[unpkt_t];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto& vars = design->top_modules[0]->variables;
  bool found = false;
  for (auto& v : vars) {
    if (v.name == "aa") {
      EXPECT_TRUE(v.is_assoc);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §7.8.5: a type that contains a real or shortreal has no defined equality
// operator and shall be an illegal index type, even when the real sits inside
// a struct member rather than being the index type itself.
TEST(UserDefinedTypeAssocArrayElaboration, StructIndexContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {real r; int i;} mixed_t;\n"
      "  int aa[mixed_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.8.5: the illegality of a real index type follows the type through a
// typedef chain, so an index named via a typedef that resolves to real is
// rejected just as a bare real would be.
TEST(UserDefinedTypeAssocArrayElaboration,
     TypedefResolvingToRealIndexRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef real real_alias_t;\n"
      "  int aa[real_alias_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.8.5: "contains a real" reaches through a struct member that is itself a
// typedef alias of real, so the real-ness has to be resolved before the index
// type can be judged legal. Such a struct is still an illegal index type.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructMemberTypedefResolvingToRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef real real_alias_t;\n"
      "  typedef struct {real_alias_t r; int i;} mixed_t;\n"
      "  int aa[mixed_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.8.5: "contains a real" reaches recursively through a nested aggregate. A
// struct member that is itself a named struct type holding a real makes the
// outer struct an illegal index type, so the check must descend into the inner
// struct's own members rather than stopping at the first level.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructWithNestedTypedefStructContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {real r;} inner_t;\n"
      "  typedef struct {inner_t x; int i;} outer_t;\n"
      "  int aa[outer_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §7.8.5: an inline (anonymous) nested struct member is written directly in the
// enclosing struct rather than through a typedef, but a real buried inside that
// inline aggregate still makes the enclosing type contain a real and therefore
// an illegal index type.
TEST(UserDefinedTypeAssocArrayElaboration,
     StructWithInlineNestedStructContainingRealRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef struct {struct {real r;} x; int i;} outer_t;\n"
      "  int aa[outer_t];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
